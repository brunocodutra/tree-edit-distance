use std::borrow::Borrow;
use std::ops::Deref;

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

impl<'t, T: 't + Deref<Target = [N]>, N: 't + Borrow<T>> Tree<'t> for T {
    type Child = N;
    type Children = &'t [N];
    fn children(&'t self) -> Self::Children {
        self
    }
}
