use std::fmt::Debug;
use std::ops::Add;

/// An abstraction for a generic tree node.
pub trait Node<'n> {
    /// A type whose values encode the [Node]'s _kind_.
    ///
    /// Only [Node]s of the equal _kind_ can replace each other.
    type Kind: PartialEq;

    /// Returns a value that encodes this [Node]'s _kind_.
    fn kind(&'n self) -> Self::Kind;

    /// A type whose values encode this [Node]'s _weight_.
    ///
    /// The default value of this type is assumed to be the additive identity (i.e. _zero_).
    type Weight: Debug + Default + Copy + PartialOrd + Add<Output = Self::Weight>;

    /// Returns the cost of inserting or deleting this [Node].
    fn weight(&'n self) -> Self::Weight;
}
