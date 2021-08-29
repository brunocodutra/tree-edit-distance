use crate::Node;
use arrayvec::ArrayVec;
use derive_more::{Add, From};
use itertools::Itertools;
use pathfinding::{num_traits::Zero, prelude::*};
use std::{borrow::Borrow, collections::HashMap, ops::Add};

/// A single operation between two [Node]s.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Edit {
    /// Swap the [Node]s and edit their children.
    Replace(Box<[Edit]>),

    /// Insert the incoming [Node] along with its children in place.
    Insert,

    /// Remove the existing [Node] along with its children.
    Remove,
}

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, From, Add)]
struct Cost<T>(T);

impl<T: Default + Eq + Add<Output = T>> Zero for Cost<T> {
    fn zero() -> Self {
        Self::default()
    }

    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

trait NodeExt: for<'n> Node<'n> {
    fn cost(&self) -> <Self as Node>::Weight;
}

impl<N, W> NodeExt for N
where
    for<'n> N: Node<'n, Weight = W>,
    W: Default + Copy + Ord + Add<Output = W>,
{
    fn cost(&self) -> W {
        self.children()
            .borrow()
            .iter()
            .map(Borrow::borrow)
            .map(NodeExt::cost)
            .fold(self.weight(), Add::add)
    }
}

fn levenshtein<N, W, R, S>(a: S, b: S) -> (Box<[Edit]>, W)
where
    for<'n> N: Node<'n, Weight = W> + NodeExt,
    W: Default + Copy + Ord + Add<Output = W>,
    R: Borrow<N>,
    S: Borrow<[R]>,
{
    let a = a.borrow();
    let b = b.borrow();

    let mut edges = HashMap::new();

    let (path, Cost(cost)) = dijkstra(
        &(0, 0),
        |&(x, y)| {
            use Edit::*;

            let a = a.get(x).map(Borrow::borrow);
            let b = b.get(y).map(Borrow::borrow);

            let mut successors = ArrayVec::<_, 3>::new();

            if let Some(a) = a {
                let next = (x + 1, y);
                let none = edges.insert(((x, y), next), Remove);
                debug_assert!(none.is_none());
                successors.push((next, a.cost().into()));
            }

            if let Some(b) = b {
                let next = (x, y + 1);
                let none = edges.insert(((x, y), next), Insert);
                debug_assert!(none.is_none());
                successors.push((next, b.cost().into()));
            }

            if let (Some(a), Some(b)) = (a, b) {
                if a.kind() == b.kind() {
                    let (inner, cost) = levenshtein(a.children(), b.children());

                    let next = (x + 1, y + 1);
                    let none = edges.insert(((x, y), next), Replace(inner));
                    debug_assert!(none.is_none());
                    successors.push((next, cost.into()));
                }
            }

            successors
        },
        |&p| p == (a.len(), b.len()),
    )
    .unwrap();

    let patches = path
        .into_iter()
        .tuple_windows()
        .flat_map(move |e| edges.remove(&e))
        .collect();

    (patches, cost)
}

/// Finds the lowest cost sequence of [Edit]s that transforms one tree of [Node]s into the other.
///
/// The sequence of [Edit]s is understood to apply to the left-hand side so it becomes the
/// right-hand side.
pub fn diff<N, W>(a: &N, b: &N) -> (Box<[Edit]>, W)
where
    for<'n> N: Node<'n, Weight = W>,
    W: Default + Copy + Ord + Add<Output = W>,
{
    levenshtein::<N, _, _, &[_]>(&[a], &[b])
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::{collection::vec, prelude::*, strategy::LazyJust};
    use std::{collections::HashSet, fmt::Debug, mem::swap};
    use test_strategy::{proptest, Arbitrary};
    use Edit::*;

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

        type Child = Self;
        type Children = &'n [Self];
        fn children(&'n self) -> Self::Children {
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

    trait Tree {
        fn nodes(&self) -> usize;
    }

    impl<N> Tree for N
    where
        for<'n> N: Node<'n>,
    {
        fn nodes(&self) -> usize {
            self.children()
                .borrow()
                .iter()
                .map(Borrow::borrow)
                .map(Tree::nodes)
                .fold(1, Add::add)
        }
    }

    impl Tree for Box<[Edit]> {
        fn nodes(&self) -> usize {
            self.iter()
                .map(|e| match e {
                    Replace(c) => c.nodes() + 1,
                    _ => 1,
                })
                .sum()
        }
    }

    #[proptest]
    fn the_number_of_edits_is_at_most_equal_to_the_total_number_of_nodes(
        a: MockNode<u8>,
        b: MockNode<u8>,
    ) {
        let (e, _) = diff(&a, &b);
        assert!(e.nodes() <= a.nodes() + b.nodes());
    }

    #[proptest]
    fn the_cost_is_at_most_equal_to_the_sum_of_costs(a: MockNode<u8>, b: MockNode<u8>) {
        let (_, c) = diff(&a, &b);
        assert!(c <= a.cost() + b.cost());
    }

    #[proptest]
    fn nodes_of_different_kinds_cannot_be_replaced(a: MockNode<NotEq>, b: MockNode<NotEq>) {
        let (e, _) = diff(&a, &b);

        assert_eq!(
            e.into_vec().into_iter().collect::<HashSet<_>>(),
            [Remove, Insert].iter().cloned().collect::<HashSet<_>>()
        );
    }

    #[proptest]
    fn nodes_of_equal_kinds_can_be_replaced(a: MockNode<Eq>, b: MockNode<Eq>) {
        let (e, _) = diff(&a, &b);
        let (i, _) = levenshtein(a.children(), b.children());
        assert_eq!(&*e, &[Replace(i)]);
    }

    #[proptest]
    fn the_cost_of_swapping_nodes_is_equal_to_the_sum_of_their_costs(
        a: MockNode<NotEq>,
        b: MockNode<NotEq>,
    ) {
        let (_, c) = diff(&a, &b);
        assert_eq!(c, a.cost() + b.cost());
    }

    #[proptest]
    fn the_cost_of_replacing_nodes_does_not_depend_on_their_weights(
        a: MockNode<Eq>,
        b: MockNode<Eq>,
    ) {
        let (_, c) = diff(&a, &b);
        assert!(c <= a.cost() - a.weight() + b.cost() - b.weight());
    }

    #[proptest]
    fn the_cost_is_always_minimized(
        #[any((1, 100).into())] mut a: MockNode<Eq>,
        #[any((1, 100).into())] mut b: MockNode<Eq>,
    ) {
        if a.children().len() > b.children().len() {
            swap(&mut a, &mut b)
        }

        let h: u64 = b
            .children()
            .iter()
            .sorted_by_key(|n| n.weight())
            .skip(b.children().len() - a.children().len())
            .map(Node::weight)
            .sum();

        let (_, c) = diff(&a, &b);
        assert_eq!(c, b.cost() - b.weight() - h);
    }
}
