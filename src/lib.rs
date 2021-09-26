//! # Overview
//!
//! This crate provides an implementation of a recursive generalized version of the
//! [Levenshtein distance][levenshtein] for arbitrary sequences that finds the smallest possible
//! diff between two trees, according to a user-defined measure for the cost of inserting and
//! removing nodes. The smallest possible diff is defined by the the lowest cost sequence of edits
//! that transforms one tree into the other.
//!
//! [levenshtein]:  https://en.wikipedia.org/wiki/Levenshtein_distance
//!
//! # Example
//!
//! ```rust
//! use tree_edit_distance::*;
//! # use json::{object, JsonValue};
//! use std::mem::{discriminant, Discriminant};
//!
//! enum Json {
//!     Null,
//!     Bool(bool),
//!     Number(f64),
//!     String(String),
//!     Array(Vec<Json>),
//!     Map(Vec<(String, Json)>),
//! }
//!
//! impl<'n> Node<'n> for Json {
//!     type Kind = Discriminant<Json>;
//!     fn kind(&self) -> Self::Kind {
//!         discriminant(self)
//!     }
//!
//!     type Weight = u64;
//!     fn weight(&self) -> Self::Weight {
//!         1
//!     }
//! }
//!
//! impl<'t> Tree<'t> for Json {
//!     type Child = &'t Self;
//!     type Children = Box<[Self::Child]>;
//!     fn children(&'t self) -> Self::Children {
//!         match self {
//!             Json::Array(a) => a.iter().collect(),
//!             Json::Map(m) => m.iter().map(|(_, v)| v).collect(),
//!             _ => Box::default(),
//!         }
//!     }
//! }
//! #
//! # impl From<JsonValue> for Json {
//! #     fn from(obj: JsonValue) -> Self {
//! #         use JsonValue::*;
//! #         match obj {
//! #             Null => Json::Null,
//! #             Boolean(b) => Json::Bool(b),
//! #             Number(n) => Json::Number(n.into()),
//! #             Short(s) => Json::String(s.into()),
//! #             String(s) => Json::String(s),
//! #             Array(a) => Json::Array(a.into_iter().map(Into::into).collect()),
//! #             Object(m) => Json::Map(
//! #                 m.iter()
//! #                     .map(|(k, v)| (k.into(), v.clone().into()))
//! #                     .collect(),
//! #             ),
//! #         }
//! #     }
//! # }
//!
//! macro_rules! json {
//!     ($( $tokens:tt )*) => {
//!         // ...
//! #         Json::from(object!($($tokens)*))
//!     };
//! }
//!
//! let john = json! {
//!     "name": "John Doe",
//!     "age": 43,
//!     "phones": [
//!         "+44 1234567",
//!         "+44 2345678"
//!     ]
//! };
//!
//! let jane = json! {
//!     "name": "Jane Doe",
//!     "maiden name": "Smith",
//!     "age": 40,
//!     "phones": [
//!         "+44 7654321",
//!     ]
//! };
//!
//! let (edits, cost) = diff(&john, &jane);
//!
//! assert_eq!(cost, 2);
//!
//! assert_eq!(&*edits, &[
//!     Edit::Replace(Box::new([
//!         Edit::Insert,                       // "name"
//!         Edit::Replace(Box::default()),      // "maiden name"
//!         Edit::Replace(Box::default()),      // "age"
//!         Edit::Replace(Box::new([            // "phones"
//!             Edit::Remove,
//!             Edit::Replace(Box::default()),
//!         ])),
//!     ]))
//! ]);
//! ```

mod diff;
mod edit;
mod tree;

pub use diff::*;
pub use edit::*;
pub use tree::*;

mod cost;
mod fold;

pub(crate) use cost::*;
pub(crate) use fold::*;
