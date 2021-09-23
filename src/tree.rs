use crate::Fold;
use std::{borrow::Borrow, ops::Deref};

/// An abstraction for a recursive tree.
pub trait Tree<'t> {
    /// A type that may be borrowed as `&Self`.
    ///
    /// This is often just `Self` or `&'t Self`, but need not necessarily be.
    type Child: Borrow<Self>;

    /// A type that holds this [Tree]'s children as a contiguous sequence (i.e. a _slice_).
    type Children: Deref<Target = [Self::Child]>;

    /// Returns this [Tree]'s immediate children.
    fn children(&'t self) -> Self::Children;
}

impl<T: ?Sized + for<'t> Tree<'t>> Fold for T {
    fn fold<R, Fn: FnMut(R, &Self) -> R>(&self, init: R, f: &mut Fn) -> R {
        self.children()
            .iter()
            .fold(f(init, self), |r, b| b.borrow().fold(r, f))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

    fn tree<V: 'static + Arbitrary>(size: Size) -> impl Strategy<Value = MockTree<V>> {
        let depth = size.depth as u32;
        let breadth = size.breadth as u32;
        let size = (breadth.pow(depth + 1) - 1) / (breadth - 1) / 2; // half the maximum number of nodes

        (any::<V>(), LazyJust::new(Vec::new))
            .prop_map_into()
            .prop_recursive(depth, size, breadth, move |inner| {
                (any::<V>(), vec(inner, ..=breadth as usize)).prop_map_into()
            })
    }

    #[derive(Debug, Default, Clone, PartialEq, Eq, Hash, From)]
    pub(crate) struct MockTree<V> {
        pub value: V,
        children: Vec<Self>,
    }

    impl<V: 'static + Arbitrary> Arbitrary for MockTree<V> {
        type Parameters = Size;
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(size: Size) -> Self::Strategy {
            tree(size).boxed()
        }
    }

    impl<'t, V: 't> Tree<'t> for MockTree<V> {
        type Child = Self;
        type Children = &'t [Self];
        fn children(&'t self) -> Self::Children {
            &self.children
        }
    }

    #[proptest]
    fn count_equals_one_plus_sum_of_count_of_children(t: MockTree<()>) {
        assert_eq!(t.count(), 1 + t.children().count());
    }
}

#[cfg(test)]
pub(crate) use tests::MockTree;
