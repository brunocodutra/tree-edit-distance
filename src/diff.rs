use crate::{Node, Tree};
use arrayvec::{ArrayVec, IntoIter};
use derivative::Derivative;
use itertools::{Itertools, Product};
use petgraph::{algo::astar, visit::*};
use std::collections::HashSet;
use std::iter::{once, FlatMap, Map, Once};
use std::ops::{Add, Deref, RangeInclusive};
use std::{borrow::Borrow, collections::HashMap, fmt::Debug, marker::PhantomData};

/// A single operation between two [Node]s.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Edit {
    /// Remove the existing [Node] along with its children.
    Remove,

    /// Insert the incoming [Node] along with its children in place.
    Insert,

    /// Swap the [Node]s and edit their children.
    Replace(Box<[Edit]>),
}

impl<'t> Tree<'t> for Edit {
    type Child = Self;
    type Children = &'t [Self];

    fn children(&'t self) -> Self::Children {
        if let Edit::Replace(c) = self {
            c
        } else {
            &[]
        }
    }
}

trait Fold {
    fn fold<R, F: FnMut(R, &Self) -> R>(&self, init: R, f: &mut F) -> R;

    fn sum<N: Default + Add<Output = N>, F: FnMut(&Self) -> N>(&self, mut f: F) -> N {
        self.fold(N::default(), &mut |n, c| n + f(c))
    }

    fn len(&self) -> usize {
        self.sum(|_| 1)
    }
}

impl<T: ?Sized> Fold for T
where
    for<'t> T: Tree<'t>,
{
    fn fold<R, F: FnMut(R, &Self) -> R>(&self, init: R, f: &mut F) -> R {
        self.children()
            .iter()
            .fold(f(init, self), |r, b| b.borrow().fold(r, f))
    }
}

#[derive(Derivative)]
#[derivative(Copy(bound = ""), Clone(bound = ""))]
enum Edge<'n, N: Node<'n>> {
    Remove(<Self as EdgeRef>::NodeId, &'n N),
    Insert(<Self as EdgeRef>::NodeId, &'n N),
    Replace(<Self as EdgeRef>::NodeId, &'n N, &'n N),
}

impl<'n, N: Node<'n>> EdgeRef for Edge<'n, N> {
    type NodeId = (usize, usize);
    type EdgeId = (Self::NodeId, Self::NodeId);
    type Weight = ();

    fn id(&self) -> Self::EdgeId {
        (self.source(), self.target())
    }

    fn source(&self) -> Self::NodeId {
        match *self {
            Edge::Remove(s, ..) => s,
            Edge::Insert(s, ..) => s,
            Edge::Replace(s, ..) => s,
        }
    }

    fn target(&self) -> Self::NodeId {
        match *self {
            Edge::Remove((i, j), ..) => (i + 1, j),
            Edge::Insert((i, j), ..) => (i, j + 1),
            Edge::Replace((i, j), ..) => (i + 1, j + 1),
        }
    }

    fn weight(&self) -> &Self::Weight {
        &()
    }
}

#[derive(Derivative)]
#[derivative(Copy(bound = ""), Clone(bound = ""))]
struct Graph<'r, R: Borrow<N>, N: Node<'r>>(&'r [R], &'r [R], PhantomData<N>);

impl<'r, R: Borrow<N>, N: Node<'r>> Graph<'r, R, N> {
    fn new(a: &'r [R], b: &'r [R]) -> Self {
        Graph(a, b, PhantomData)
    }
}

impl<'r, R: Borrow<N>, N: Node<'r>> GraphBase for Graph<'r, R, N> {
    type NodeId = <Edge<'r, N> as EdgeRef>::NodeId;
    type EdgeId = <Edge<'r, N> as EdgeRef>::EdgeId;
}

impl<'r, R: Borrow<N>, N: Node<'r>> GraphRef for Graph<'r, R, N> {}

impl<'r, R: Borrow<N>, N: Node<'r>> Data for Graph<'r, R, N> {
    type NodeWeight = ();
    type EdgeWeight = <Edge<'r, N> as EdgeRef>::Weight;
}

impl<'r, R: Borrow<N>, N: 'r + Node<'r>> IntoNeighbors for Graph<'r, R, N> {
    type Neighbors = Map<
        IntoIter<<Self as IntoEdgeReferences>::EdgeRef, 3>,
        fn(<Self as IntoEdgeReferences>::EdgeRef) -> Self::NodeId,
    >;

    fn neighbors(self, id: Self::NodeId) -> Self::Neighbors {
        self.edges(id).map(|e| e.target())
    }
}

impl<'r, R: Borrow<N>, N: 'r + Node<'r>> IntoEdgeReferences for Graph<'r, R, N> {
    type EdgeRef = Edge<'r, N>;
    type EdgeReferences = FlatMap<
        Product<Product<Once<Self>, RangeInclusive<usize>>, RangeInclusive<usize>>,
        IntoIter<Self::EdgeRef, 3>,
        fn(((Self, usize), usize)) -> IntoIter<Self::EdgeRef, 3>,
    >;

    fn edge_references(self) -> Self::EdgeReferences {
        once(self)
            .cartesian_product(0..=self.0.len())
            .cartesian_product(0..=self.1.len())
            .flat_map(|((g, i), j)| g.edges((i, j)))
    }
}

impl<'r, R: Borrow<N>, N: 'r + Node<'r>> IntoEdges for Graph<'r, R, N> {
    type Edges = IntoIter<Self::EdgeRef, 3>;

    fn edges(self, (i, j): Self::NodeId) -> Self::Edges {
        let a = self.0.get(i).map(Borrow::borrow);
        let b = self.1.get(j).map(Borrow::borrow);

        let mut edges = ArrayVec::<_, 3>::new();

        if let Some(a) = a {
            edges.push(Edge::Remove((i, j), a));
        }

        if let Some(b) = b {
            edges.push(Edge::Insert((i, j), b));
        }

        if let (Some(a), Some(b)) = (a, b) {
            if a.kind() == b.kind() {
                edges.push(Edge::Replace((i, j), a, b));
            }
        }

        edges.into_iter()
    }
}

impl<'r, R: Borrow<N>, N: 'r + Node<'r>> NodeCount for Graph<'r, R, N> {
    fn node_count(self: &Self) -> usize {
        (self.0.len() + 1) * (self.1.len() + 1)
    }
}

impl<'r, R: Borrow<N>, N: 'r + Node<'r>> Visitable for Graph<'r, R, N> {
    type Map = HashSet<Self::NodeId>;

    fn visit_map(self: &Self) -> Self::Map {
        HashSet::with_capacity(self.node_count())
    }

    fn reset_map(self: &Self, map: &mut Self::Map) {
        map.clear();
        map.reserve(self.node_count().saturating_sub(map.capacity()))
    }
}

fn levenshtein<N, W, R, S>(a: S, b: S) -> (Box<[Edit]>, W)
where
    for<'n> N: Node<'n, Weight = W> + Tree<'n>,
    W: Debug + Default + Copy + Ord + Add<Output = W>,
    R: Borrow<N>,
    S: Deref<Target = [R]>,
{
    let mut edges = HashMap::new();

    let (cost, path) = astar(
        Graph::new(&a, &b),
        (0, 0),
        |p| p == (a.len(), b.len()),
        |e| {
            let (_, cost) = edges.entry(e.id()).or_insert_with(|| match e {
                Edge::Remove(_, n) => (Edit::Remove, n.sum(|n| n.weight())),
                Edge::Insert(_, n) => (Edit::Insert, n.sum(|n| n.weight())),
                Edge::Replace(_, a, b) => {
                    let (inner, w) = levenshtein(a.children(), b.children());
                    (Edit::Replace(inner), w)
                }
            });

            *cost
        },
        |_| N::Weight::default(),
    )
    .unwrap();

    let patches = path
        .into_iter()
        .tuple_windows()
        .flat_map(move |e| edges.remove(&e))
        .map(|(e, _)| e)
        .collect();

    (patches, cost)
}

/// Finds the lowest cost sequence of [Edit]s that transforms one tree of [Node]s into the other.
///
/// The sequence of [Edit]s is understood to apply to the left-hand side so it becomes the
/// right-hand side.
pub fn diff<N, W>(a: &N, b: &N) -> (Box<[Edit]>, W)
where
    for<'n> N: Node<'n, Weight = W> + Tree<'n>,
    W: Debug + Default + Copy + Ord + Add<Output = W>,
{
    levenshtein::<N, _, _, &[_]>(&[a], &[b])
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use derive_more::From;
    use proptest::collection::{size_range, vec};
    use proptest::{prelude::*, strategy::LazyJust};
    use test_strategy::{proptest, Arbitrary};

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
    pub struct Size {
        depth: usize,
        breadth: usize,
    }

    impl Default for Size {
        fn default() -> Self {
            (3, 5).into()
        }
    }

    fn node<K: 'static + Arbitrary>(
        children: impl Strategy<Value = Vec<MockNode<K>>>,
    ) -> impl Strategy<Value = MockNode<K>> {
        (any::<K>(), 1..100u64, children).prop_map_into()
    }

    fn nodes<K: 'static + Arbitrary>(size: Size) -> impl Strategy<Value = MockNode<K>> {
        let d = size.depth as u32;
        let b = size.breadth as u32;
        let s = b.pow(d);

        node(LazyJust::new(Vec::new))
            .prop_recursive(d, s, b, move |inner| node(vec(inner, 0..=b as usize)))
    }

    #[derive(Debug, Default, Clone, From)]
    struct MockNode<K> {
        kind: K,
        weight: u64,
        children: Vec<MockNode<K>>,
    }

    impl<K: 'static + Arbitrary> Arbitrary for MockNode<K> {
        type Parameters = Size;
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(size: Size) -> Self::Strategy {
            nodes(size).boxed()
        }
    }

    impl<'n, K: 'n + PartialEq> Node<'n> for MockNode<K> {
        type Kind = &'n K;
        fn kind(&'n self) -> Self::Kind {
            &self.kind
        }

        type Weight = u64;
        fn weight(&self) -> Self::Weight {
            self.weight
        }
    }

    impl<'t, K: 't> Tree<'t> for MockNode<K> {
        type Child = Self;
        type Children = &'t [Self];
        fn children(&'t self) -> Self::Children {
            &self.children
        }
    }

    #[derive(Debug, Default, Clone, Eq, PartialEq, Arbitrary)]
    struct Eq;

    #[derive(Debug, Default, Clone, Arbitrary)]
    struct NotEq;

    impl PartialEq for NotEq {
        fn eq(&self, _: &Self) -> bool {
            false
        }
    }

    #[proptest]
    fn the_number_of_edits_is_at_most_equal_to_the_total_number_of_nodes(
        a: MockNode<u8>,
        b: MockNode<u8>,
    ) {
        let (e, _) = diff(&a, &b);
        let edits: usize = e.iter().map(Edit::len).sum();
        assert_matches!((edits, a.len() + b.len()), (x, y) if x <= y);
    }

    #[proptest]
    fn the_cost_is_at_most_equal_to_the_sum_of_costs(a: MockNode<u8>, b: MockNode<u8>) {
        let (_, c) = diff(&a, &b);
        assert_matches!((c, a.sum(|n| n.weight()) + b.sum(|n| n.weight())), (x, y) if x <= y);
    }

    #[proptest]
    fn the_cost_between_identical_trees_cis_zero(a: MockNode<u8>) {
        let (e, c) = diff(&a, &a);
        let edits: usize = e.iter().map(Edit::len).sum();
        assert_eq!(edits, a.len());
        assert_eq!(c, 0);
    }

    #[proptest]
    fn nodes_of_different_kinds_cannot_be_replaced(a: MockNode<NotEq>, b: MockNode<NotEq>) {
        use Edit::*;

        let (e, _) = diff(&a, &b);
        assert_matches!(&e[..], [Remove, Insert] | [Insert, Remove]);
    }

    #[proptest]
    fn nodes_of_equal_kinds_can_be_replaced(a: MockNode<Eq>, b: MockNode<Eq>) {
        let (e, _) = diff(&a, &b);
        let (i, _) = levenshtein(a.children(), b.children());

        assert_matches!(&e[..], [Edit::Replace(x)] => {
            assert_eq!(x, &i);
        });
    }

    #[proptest]
    fn the_cost_of_swapping_nodes_is_equal_to_the_sum_of_their_costs(
        a: MockNode<NotEq>,
        b: MockNode<NotEq>,
    ) {
        let (_, c) = diff(&a, &b);
        assert_eq!(c, a.sum(|n| n.weight()) + b.sum(|n| n.weight()));
    }

    #[proptest]
    fn the_cost_of_replacing_nodes_does_not_depend_on_their_weights(
        a: MockNode<Eq>,
        b: MockNode<Eq>,
    ) {
        let (_, c) = diff(&a, &b);
        let (_, d) = levenshtein(a.children(), b.children());
        assert_eq!(c, d);
    }

    #[proptest]
    fn the_cost_is_always_minimized(
        #[any(size_range(1..16).lift())] a: Vec<MockNode<u8>>,
        #[any(size_range(1..16).lift())] b: Vec<MockNode<u8>>,
        #[strategy(0..#a.len())] i: usize,
        #[strategy(0..#b.len())] j: usize,
    ) {
        let mut x = a.clone();
        let mut y = b.clone();

        let m = x.remove(i);
        let n = y.remove(j);

        let (_, c) = levenshtein(a, b);
        let (_, d) = levenshtein(x, y);

        assert_matches!((c, d + m.sum(|n| n.weight()) + n.sum(|n| n.weight())), (x, y) if x <= y);
    }
}
