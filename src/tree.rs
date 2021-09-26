use std::ops::Add;

/// An abstraction for a generic tree node.
pub trait Node<'n> {
    /// The type of this [Node]'s [kind][Node::kind].
    ///
    /// Only [Node]s of the equal _kind_ can replace each other.
    type Kind: PartialEq;

    /// Returns this [Node]'s _kind_.
    fn kind(&'n self) -> Self::Kind;

    /// The type of this [Node]'s [weight][Node::weight].
    ///
    /// The default value of this type is assumed to be the additive identity (i.e. _zero_).
    type Weight: Default + Copy + Ord + Add<Output = Self::Weight>;

    /// Returns the cost of inserting or deleting this [Node].
    ///
    /// A [Node]'s weight should be independent of the weight of its children.
    fn weight(&'n self) -> Self::Weight;
}

/// An abstraction for a recursive tree.
pub trait Tree<'t>: 't + Node<'t> {
    /// A type that can iterate over this [Tree]'s [children][Tree::children].
    type Children: IntoIterator<Item = &'t Self>;

    /// Returns this [Tree]'s immediate children.
    fn children(&'t self) -> Self::Children;
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
            (5, 5).into()
        }
    }

    fn tree<K: 'static + PartialEq + Arbitrary>(size: Size) -> impl Strategy<Value = MockTree<K>> {
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
    pub(crate) struct MockTree<K: PartialEq> {
        kind: K,
        weight: u8,
        children: Vec<Self>,
    }

    impl<K: 'static + PartialEq + Arbitrary> Arbitrary for MockTree<K> {
        type Parameters = Size;
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(size: Size) -> Self::Strategy {
            tree(size).boxed()
        }
    }

    impl<'n, K: 'n + PartialEq> Node<'n> for MockTree<K> {
        type Kind = &'n K;
        fn kind(&'n self) -> Self::Kind {
            &self.kind
        }

        type Weight = u64;
        fn weight(&'n self) -> Self::Weight {
            self.weight.into()
        }
    }

    impl<'t, K: 't + PartialEq> Tree<'t> for MockTree<K> {
        type Children = &'t [Self];
        fn children(&'t self) -> Self::Children {
            &self.children
        }
    }

    impl<K: PartialEq> Fold for MockTree<K>
    where
        Self: for<'t> Tree<'t, Children = &'t [Self]>,
    {
        fn fold<R, Fn: FnMut(R, &Self) -> R>(&self, init: R, f: &mut Fn) -> R {
            self.children().fold(f(init, self), f)
        }
    }

    impl<K: PartialEq, W: Default + Copy + Add<Output = W>> Cost for MockTree<K>
    where
        Self: for<'t> Tree<'t, Weight = W, Children = &'t [Self]>,
    {
        type Output = W;

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
