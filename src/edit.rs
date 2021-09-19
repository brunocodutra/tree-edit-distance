use crate::Tree;

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

impl<'t> Tree<'t> for Edit {
    type Child = Self;
    type Children = &'t [Self];

    fn children(&'t self) -> Self::Children {
        if let Edit::Replace(c) = self {
            c
        } else {
            &[]
        }
    }
}
