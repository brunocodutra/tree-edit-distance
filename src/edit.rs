/// A single operation between two [Node][crate::Node]s.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Edit {
    /// Swap the [Node][crate::Node]s and edit their children.
    Replace(Box<[Edit]>),

    /// Insert the incoming [Node][crate::Node] along with its children in place.
    Insert,

    /// Remove the existing [Node][crate::Node] along with its children.
    Remove,
}

#[cfg(test)]
impl crate::Fold for Edit {
    #[inline]
    fn fold<R, Fn: FnMut(R, &Self) -> R>(&self, init: R, f: &mut Fn) -> R {
        if let Edit::Replace(c) = self {
            c.fold(f(init, self), f)
        } else {
            f(init, self)
        }
    }
}
