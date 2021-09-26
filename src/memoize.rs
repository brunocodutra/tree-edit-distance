use crate::{Cost, Node, Tree};
use std::ops::Add;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub(crate) struct Memoized<'t, T: Tree<'t>> {
    tree: &'t T,
    cost: T::Weight,
    children: Box<[Self]>,
}

impl<'t, T: 't + Tree<'t>> Node<'t> for Memoized<'t, T> {
    type Kind = T::Kind;

    #[inline]
    fn kind(&'t self) -> Self::Kind {
        T::kind(self.tree)
    }

    type Weight = T::Weight;

    #[inline]
    fn weight(&'t self) -> Self::Weight {
        T::weight(self.tree)
    }
}

impl<'t, T: 't + Tree<'t>> Tree<'t> for Memoized<'t, T> {
    type Children = &'t [Self];

    #[inline]
    fn children(&'t self) -> Self::Children {
        &self.children
    }
}

impl<'t, T: Tree<'t, Weight = W>, W: Copy + Default + Add<Output = W>> Cost for Memoized<'t, T> {
    type Output = W;

    #[inline]
    fn cost(&self) -> Self::Output {
        self.cost
    }
}

pub(crate) fn memoize<T, W>(t: &T) -> Memoized<T>
where
    T: for<'t> Tree<'t, Weight = W>,
    W: Copy + Default + Add<Output = W>,
{
    let children: Box<[_]> = t.children().into_iter().map(memoize).collect();

    Memoized {
        tree: t,
        cost: t.weight() + children.cost(),
        children,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MockTree;
    use test_strategy::proptest;

    #[proptest]
    fn kind_is_preserved(t: MockTree<()>) {
        assert_eq!(memoize(&t).kind(), t.kind());
    }

    #[proptest]
    fn weight_is_preserved(t: MockTree<()>) {
        assert_eq!(memoize(&t).weight(), t.weight());
    }

    #[proptest]
    fn cost_is_memoized(t: MockTree<()>) {
        let u = memoize(&t);
        assert_eq!(u.cost, t.cost());
        assert_eq!(u.cost, u.cost());
    }
}
