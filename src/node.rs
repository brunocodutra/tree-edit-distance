use std::{borrow::Borrow, ops::Add};

/// An abstraction for a generic tree.
pub trait Node<'n> {
    /// A type whose values encode the [Node]'s _kind_.
    ///
    /// Only [Node]s of the same _kind_ can be replaced by one another.
    type Kind: Eq;

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

    /// A type that may be borrowed as `&Self`.
    ///
    /// This is often just `Self` or `&'n Self`, but need not necessarily be.
    type Child: Borrow<Self>;

    /// A type that holds this [Node]'s children as a contiguous sequence (i.e. a _slice_).
    type Children: Borrow<[Self::Child]>;

    /// Returns this [Node]'s children.
    fn children(&'n self) -> Self::Children;
}
