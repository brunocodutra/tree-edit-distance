use std::ops::Add;

/// An abstraction for a generic tree node.
pub trait Node {
    /// The type of this [Node]'s [kind][Node::kind].
    ///
    /// Only [Node]s of the equal _kind_ can replace each other.
    type Kind: PartialEq;

    /// Returns this [Node]'s _kind_.
    fn kind(&self) -> Self::Kind;

    /// The type of this [Node]'s [weight][Node::weight].
    ///
    /// The default value of this type is assumed to be the additive identity (i.e. _zero_).
    type Weight: Default + Copy + Ord + Add<Output = Self::Weight>;

    /// Returns the cost of inserting or deleting this [Node].
    ///
    /// A [Node]'s weight should be independent of the weight of its children.
    fn weight(&self) -> Self::Weight;
}

/// An abstraction for a recursive tree.
pub trait Tree: Node {
    /// A type that can iterate over this [Tree]'s [children][Tree::children].
    type Children<'c>: 'c + IntoIterator<Item = &'c Self>
    where
        Self: 'c;

    /// Returns this [Tree]'s immediate children.
    fn children(&self) -> Self::Children<'_>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Cost, Fold};
    use derive_more::From;
    use proptest::{collection::vec, prelude::*, strategy::LazyJust};
    use test_strategy::proptest;

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
    pub struct Size {
        depth: usize,
        breadth: usize,
    }

    impl Default for Size {
        fn default() -> Self {
            #[cfg(not(miri))]
            {
                (5, 5).into()
            }

            #[cfg(miri)]
            {
                (2, 2).into()
            }
        }
    }

    fn tree<K>(size: Size) -> impl Strategy<Value = MockTree<K>>
    where
        K: 'static + Copy + PartialEq + Arbitrary,
    {
        let depth = size.depth as u32;
        let breadth = size.breadth as u32;
        let size = (breadth.pow(depth + 1) - 1) / (breadth - 1) / 2; // half the maximum number of nodes

        (any::<K>(), any::<u8>(), LazyJust::new(Vec::new))
            .prop_map_into()
            .prop_recursive(depth, size, breadth, move |inner| {
                (any::<K>(), any::<u8>(), vec(inner, ..=breadth as usize)).prop_map_into()
            })
    }

    #[derive(Debug, Default, Clone, PartialEq, Eq, Hash, From)]
    pub(crate) struct MockTree<K: Copy + PartialEq> {
        kind: K,
        weight: u8,
        children: Vec<Self>,
    }

    impl<K: 'static + Copy + PartialEq + Arbitrary> Arbitrary for MockTree<K> {
        type Parameters = Size;
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(size: Size) -> Self::Strategy {
            tree(size).boxed()
        }
    }

    impl<K: Copy + PartialEq> Node for MockTree<K> {
        type Kind = K;
        fn kind(&self) -> Self::Kind {
            self.kind
        }

        type Weight = u64;
        fn weight(&self) -> Self::Weight {
            self.weight.into()
        }
    }

    impl<K: Copy + PartialEq> Tree for MockTree<K> {
        type Children<'c> = &'c [Self]
        where
            Self: 'c;

        fn children(&self) -> Self::Children<'_> {
            &self.children
        }
    }

    impl<K: Copy + PartialEq> Fold for MockTree<K> {
        fn fold<R, Fn: FnMut(R, &Self) -> R>(&self, init: R, f: &mut Fn) -> R {
            self.children().fold(f(init, self), f)
        }
    }

    impl<K: Copy + PartialEq> Cost for MockTree<K> {
        type Output = <Self as Node>::Weight;

        #[inline]
        fn cost(&self) -> Self::Output {
            self.sum(|c| c.weight())
        }
    }

    #[proptest]
    fn count_equals_one_plus_sum_of_count_of_children(t: MockTree<()>) {
        assert_eq!(t.count(), 1 + t.children().count());
    }

    #[proptest]
    fn cost_equals_weight_plus_sum_of_costs_of_children(t: MockTree<()>) {
        assert_eq!(t.cost(), t.weight() + t.children().cost());
    }
}

#[cfg(test)]
pub(crate) use tests::MockTree;
