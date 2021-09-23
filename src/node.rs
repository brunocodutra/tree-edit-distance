use crate::{Fold, Tree};
use std::ops::Add;

/// An abstraction for a generic tree node.
pub trait Node<'n>: Tree<'n> {
    /// A type whose values encode the [Node]'s _kind_.
    ///
    /// Only [Node]s of the equal _kind_ can replace each other.
    type Kind: PartialEq;

    /// Returns a value that encodes this [Node]'s _kind_.
    fn kind(&'n self) -> Self::Kind;

    /// A type whose values encode this [Node]'s _weight_.
    ///
    /// The default value of this type is assumed to be the additive identity (i.e. _zero_).
    type Weight: Default + Copy + Ord + Add<Output = Self::Weight>;

    /// Returns the cost of inserting or deleting this [Node].
    ///
    /// A [Node]'s weight should be independent of the weight of its children.
    fn weight(&'n self) -> Self::Weight;
}

pub(crate) trait NodeExt: for<'n> Node<'n, Weight = Self::Cost> {
    type Cost: Default + Add<Output = Self::Cost>;

    #[inline]
    fn cost(&self) -> Self::Cost {
        self.sum(|n| n.weight())
    }
}

impl<N: ?Sized, W> NodeExt for N
where
    N: for<'n> Node<'n, Weight = W>,
    W: Default + Add<Output = W>,
{
    type Cost = W;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MockTree;
    use test_strategy::proptest;

    pub(crate) type MockNode<K> = MockTree<(K, u8)>;

    impl<'n, K: 'n + PartialEq> Node<'n> for MockNode<K> {
        type Kind = &'n K;
        fn kind(&'n self) -> Self::Kind {
            &self.value.0
        }

        type Weight = u64;
        fn weight(&'n self) -> Self::Weight {
            self.value.1.into()
        }
    }

    #[proptest]
    fn cost_equals_weight_plus_sum_of_costs_of_children(n: MockNode<()>) {
        assert_eq!(
            n.cost(),
            n.weight() + n.children().iter().map(MockNode::cost).sum::<u64>()
        );
    }
}

#[cfg(test)]
pub(crate) use tests::MockNode;
