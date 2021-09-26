use crate::{Cost, Edit, Tree};
use arrayvec::ArrayVec;
use derive_more::{Add, From};
use itertools::Itertools;
use pathfinding::{num_traits::Zero, prelude::*};
use std::ops::{Add, Deref};
use std::{borrow::Borrow, collections::HashMap};

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, From, Add)]
struct WholeNumber<T>(T);

impl<T: Default + Eq + Add<Output = T>> Zero for WholeNumber<T> {
    fn zero() -> Self {
        Self::default()
    }

    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

fn levenshtein<T, W, B, D>(a: D, b: D) -> (Box<[Edit]>, W)
where
    T: for<'t> Tree<'t, Weight = W>,
    W: Default + Copy + Ord + Add<Output = W>,
    B: Borrow<T>,
    D: Deref<Target = [B]>,
{
    let mut edges = HashMap::new();

    let (path, WholeNumber(cost)) = astar(
        &(0, 0),
        |&(i, j)| {
            let x = a.get(i).map(B::borrow);
            let y = b.get(j).map(B::borrow);

            let mut successors = ArrayVec::<_, 3>::new();

            if let Some(x) = x {
                let next = (i + 1, j);
                let none = edges.insert(((i, j), next), Edit::Remove);
                debug_assert!(none.is_none());
                successors.push((next, x.cost().into()));
            }

            if let Some(y) = y {
                let next = (i, j + 1);
                let none = edges.insert(((i, j), next), Edit::Insert);
                debug_assert!(none.is_none());
                successors.push((next, y.cost().into()));
            }

            if let (Some(x), Some(y)) = (x, y) {
                if x.kind() == y.kind() {
                    let next = (i + 1, j + 1);
                    let (inner, cost) = levenshtein(x.children(), y.children());
                    let none = edges.insert(((i, j), next), Edit::Replace(inner));
                    debug_assert!(none.is_none());
                    successors.push((next, cost.into()));
                }
            }

            successors
        },
        |&(i, j)| match (&a[i..], &b[j..]) {
            (&[], rest) | (rest, &[]) => rest
                .iter()
                .fold(WholeNumber::default(), |r, t| r + t.borrow().cost().into()),

            (a, b) if a.len() != b.len() => {
                let rest = if a.len() > b.len() { a } else { b };
                let nth = a.len().max(b.len()) - a.len().min(b.len());
                let mut costs: Box<[_]> = rest.iter().map(B::borrow).map(T::cost).collect();
                let (cheapest, _, _) = costs.select_nth_unstable(nth);
                cheapest
                    .iter()
                    .fold(WholeNumber::default(), |r, &c| r + c.into())
            }

            _ => WholeNumber::default(),
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

/// Finds the lowest cost sequence of [Edit]s that transforms one [Tree] into the other.
///
/// The sequence of [Edit]s is understood to apply to the left-hand side so it becomes the
/// right-hand side.
pub fn diff<T, W>(a: &T, b: &T) -> (Box<[Edit]>, W)
where
    T: for<'t> Tree<'t, Weight = W>,
    W: Default + Copy + Ord + Add<Output = W>,
{
    levenshtein::<T, _, _, &[_]>(&[a], &[b])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Fold, MockTree, Tree};
    use assert_matches::assert_matches;
    use proptest::collection::size_range;
    use test_strategy::{proptest, Arbitrary};

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
        a: MockTree<u8>,
        b: MockTree<u8>,
    ) {
        let (e, _) = diff(&a, &b);
        assert_matches!((e.count(), a.count() + b.count()), (x, y) if x <= y);
    }

    #[proptest]
    fn the_cost_is_at_most_equal_to_the_sum_of_costs(a: MockTree<u8>, b: MockTree<u8>) {
        let (_, c) = diff(&a, &b);
        assert_matches!((c, a.cost() + b.cost()), (x, y) if x <= y);
    }

    #[proptest]
    fn the_cost_between_identical_trees_is_zero(a: MockTree<u8>) {
        let (e, c) = diff(&a, &a);
        assert_eq!(e.count(), a.count());
        assert_eq!(c, 0);
    }

    #[proptest]
    fn nodes_of_different_kinds_cannot_be_replaced(a: MockTree<NotEq>, b: MockTree<NotEq>) {
        use Edit::*;
        let (e, _) = diff(&a, &b);
        assert_matches!(&e[..], [Remove, Insert] | [Insert, Remove]);
    }

    #[proptest]
    fn nodes_of_equal_kinds_can_be_replaced(a: MockTree<Eq>, b: MockTree<Eq>) {
        let (e, _) = diff(&a, &b);
        let (i, _) = levenshtein(a.children(), b.children());

        assert_matches!(&e[..], [Edit::Replace(x)] => {
            assert_eq!(x, &i);
        });
    }

    #[proptest]
    fn the_cost_of_swapping_nodes_is_equal_to_the_sum_of_their_costs(
        a: MockTree<NotEq>,
        b: MockTree<NotEq>,
    ) {
        let (_, c) = diff(&a, &b);
        assert_eq!(c, a.cost() + b.cost());
    }

    #[proptest]
    fn the_cost_of_replacing_nodes_does_not_depend_on_their_weights(
        a: MockTree<Eq>,
        b: MockTree<Eq>,
    ) {
        let (_, c) = diff(&a, &b);
        let (_, d) = levenshtein(a.children(), b.children());
        assert_eq!(c, d);
    }

    #[proptest]
    fn the_cost_is_always_minimized(
        #[any(size_range(1..16).lift())] a: Vec<MockTree<u8>>,
        #[any(size_range(1..16).lift())] b: Vec<MockTree<u8>>,
        #[strategy(0..#a.len())] i: usize,
        #[strategy(0..#b.len())] j: usize,
    ) {
        let mut x = a.clone();
        let mut y = b.clone();

        let m = x.remove(i);
        let n = y.remove(j);

        let (_, c) = levenshtein(a, b);
        let (_, d) = levenshtein(x, y);

        assert_matches!((c, d + m.cost() + n.cost()), (x, y) if x <= y);
    }
}
