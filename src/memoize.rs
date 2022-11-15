use crate::{Cost, Node, Tree};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub(crate) struct Memoized<'t, T: 't + Tree> {
    tree: &'t T,
    cost: T::Weight,
    children: Box<[Self]>,
}

impl<'t, T: 't + Tree> Node for Memoized<'t, T> {
    type Kind = T::Kind;

    #[inline]
    fn kind(&self) -> Self::Kind {
        T::kind(self.tree)
    }

    type Weight = T::Weight;

    #[inline]
    fn weight(&self) -> Self::Weight {
        T::weight(self.tree)
    }
}

impl<'t, T: 't + Tree> Tree for Memoized<'t, T> {
    type Children<'c> = &'c [Self]
    where
        Self: 'c;

    #[inline]
    fn children(&self) -> Self::Children<'_> {
        &self.children
    }
}

impl<'t, T: 't + Tree> Cost for Memoized<'t, T> {
    type Output = T::Weight;

    #[inline]
    fn cost(&self) -> Self::Output {
        self.cost
    }
}

pub(crate) fn memoize<T: Tree>(t: &T) -> Memoized<T> {
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
    fn kind_is_preserved(t: MockTree<u8>) {
        assert_eq!(memoize(&t).kind(), t.kind());
    }

    #[proptest]
    fn weight_is_preserved(t: MockTree<u8>) {
        assert_eq!(memoize(&t).weight(), t.weight());
    }

    #[proptest]
    fn cost_is_memoized(t: MockTree<u8>) {
        let u = memoize(&t);
        assert_eq!(u.cost, t.cost());
        assert_eq!(u.cost, u.cost());
    }
}
