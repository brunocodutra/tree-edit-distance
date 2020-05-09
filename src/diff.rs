use crate::Node;
use arrayvec::ArrayVec;
use derive_more::Add;
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

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Add)]
struct Cost<T>(T);

impl<T: Default + Eq + Add<Output = T>> Zero for Cost<T> {
    fn zero() -> Self {
        Self::default()
    }

    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

impl<T> Cost<T> {}

trait NodeExt {
    type Cost: Zero + Ord + Copy;
    fn cost(&self) -> Self::Cost;
}

impl<N, W> NodeExt for N
where
    for<'n> N: Node<'n, Weight = W>,
    W: Default + Copy + Ord + Add<Output = W>,
{
    type Cost = Cost<W>;
    fn cost(&self) -> Self::Cost {
        self.children()
            .borrow()
            .iter()
            .map(Borrow::borrow)
            .map(NodeExt::cost)
            .fold(Cost(self.weight()), Add::add)
    }
}

fn levenshtein<N, R, S>(a: S, b: S) -> (Box<[Edit]>, N::Cost)
where
    for<'n> N: Node<'n> + NodeExt,
    R: Borrow<N>,
    S: Borrow<[R]>,
{
    let a = a.borrow();
    let b = b.borrow();

    let mut edges = HashMap::new();

    let (path, cost) = dijkstra(
        &(0, 0),
        |&(x, y)| {
            use Edit::*;

            let a = a.get(x).map(Borrow::borrow);
            let b = b.get(y).map(Borrow::borrow);

            let mut successors = ArrayVec::<[_; 3]>::new();

            if let Some(a) = a {
                let next = (x + 1, y);
                let none = edges.insert(((x, y), next), Remove);
                debug_assert!(none.is_none());
                successors.push((next, a.cost()));
            }

            if let Some(b) = b {
                let next = (x, y + 1);
                let none = edges.insert(((x, y), next), Insert);
                debug_assert!(none.is_none());
                successors.push((next, b.cost()));
            }

            if let (Some(a), Some(b)) = (a, b) {
                if a.kind() == b.kind() {
                    let (inner, cost) = levenshtein(a.children(), b.children());

                    let next = (x + 1, y + 1);
                    let none = edges.insert(((x, y), next), Replace(inner));
                    debug_assert!(none.is_none());
                    successors.push((next, cost));
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
    let (e, Cost(c)) = levenshtein::<N, _, &[_]>(&[a], &[b]);
    (e, c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use derivative::Derivative;
    use proptest::{collection::vec, prelude::*};
    use std::{collections::HashSet, fmt::Debug};
    use Edit::*;

    #[cfg(test)]
    #[derive(Derivative)]
    #[derivative(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
    pub struct Size {
        #[derivative(Default(value = "3"))]
        depth: usize,

        #[derivative(Default(value = "5"))]
        breadth: usize,
    }

    #[derive(Debug, Default, Clone, Eq, PartialEq)]
    struct MockNode<K> {
        kind: K,
        weight: u64,
        children: Vec<MockNode<K>>,
    }

    impl<K: 'static + Arbitrary> Arbitrary for MockNode<K> {
        type Parameters = Size;
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(size: Size) -> Self::Strategy {
            let d = size.depth;
            let b = size.breadth;
            let size = b.pow(d as u32);

            (any::<K>(), (1u16..).prop_map_into())
                .prop_map(|(kind, weight)| MockNode {
                    kind,
                    weight,
                    children: vec![],
                })
                .prop_recursive(d as u32, size as u32, b as u32, move |inner| {
                    (any::<K>(), (1u16..).prop_map_into(), vec(inner, 0..=b)).prop_map(
                        |(kind, weight, children)| MockNode {
                            kind,
                            weight,
                            children,
                        },
                    )
                })
                .boxed()
        }
    }

    impl<'n, K: 'n + Eq> Node<'n> for MockNode<K> {
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

    #[derive(Debug, Default, Clone)]
    struct Neq;

    impl Eq for Neq {}

    impl PartialEq for Neq {
        fn eq(&self, _: &Self) -> bool {
            false
        }
    }

    impl Arbitrary for Neq {
        type Parameters = ();
        type Strategy = Just<Self>;

        fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
            Just(Neq)
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

    proptest! {
        #[test]
        fn the_number_of_edits_is_at_most_equal_to_the_total_number_of_nodes(a: MockNode<char>, b: MockNode<char>) {
            let (e, _) = diff(&a, &b);
            assert!(e.nodes() <= a.nodes() + b.nodes());
        }

        #[test]
        fn nodes_of_different_kinds_cannot_be_replaced(a: MockNode<Neq>, b: MockNode<Neq>) {
            let (e, _) = diff(&a, &b);

            assert_eq!(
                e.into_vec().into_iter().collect::<HashSet<_>>(),
                [Remove, Insert].iter().cloned().collect::<HashSet<_>>()
            );
        }

        #[test]
        fn nodes_of_equal_kinds_can_be_replaced(a: MockNode<()>, b: MockNode<()>) {
            let (e, _) = diff(&a, &b);
            let (i, _) = levenshtein(a.children(), b.children());
            assert_eq!(&*e, &[Replace(i)]);
        }

        #[test]
        fn the_cost_of_swapping_nodes_is_equal_to_the_sum_of_their_costs(a: MockNode<Neq>, b: MockNode<Neq>) {
            let (_, c) = diff(&a, &b);
            assert_eq!(c, a.cost().0 + b.cost().0);
        }

        #[test]
        fn the_cost_of_replacing_nodes_does_not_depend_on_their_weights(a: MockNode<()>, b: MockNode<()>) {
            let (_, c) = diff(&a, &b);
            assert!(c <= a.cost().0 - a.weight() + b.cost().0 - b.weight());
        }

        #[test]
        fn the_cost_is_minimized(x: Vec<MockNode<()>>) {
            let y = vec![MockNode {
                kind: (),
                weight: 1,
                children: vec![],
            }];

            let a = MockNode {
                kind: (),
                weight: 1,
                children: y.clone(),
            };

            let b = MockNode {
                kind: (),
                weight: 1,
                children: vec![x, y].concat(),
            };

            let heaviest = b.children().iter().max_by_key(|n| n.weight()).unwrap();

            let (_, c) = diff(&a, &b);
            assert_eq!(c, b.cost().0 - b.weight() - heaviest.weight());
        }
    }
}
