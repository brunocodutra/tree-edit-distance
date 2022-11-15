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
//! use std::mem::{discriminant, Discriminant};
//! use std::iter::empty;
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
//! impl Node for Json {
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
//! impl Tree for Json {
//!     type Children<'c> = Box<dyn Iterator<Item = &'c Self> + 'c>
//!     where
//!         Self: 'c;
//!
//!     fn children(&self) -> Self::Children<'_> {
//!         match self {
//!             Json::Array(a) => Box::new(a.iter()),
//!             Json::Map(m) => Box::new(m.iter().map(|(_, v)| v)),
//!             _ => Box::new(empty()),
//!         }
//!     }
//! }
//! #
//! # impl From<serde_json::Value> for Json {
//! #     fn from(obj: serde_json::Value) -> Self {
//! #         use serde_json::Value::*;
//! #         match obj {
//! #             Null => Json::Null,
//! #             Bool(b) => Json::Bool(b),
//! #             Number(n) => Json::Number(n.as_i64().unwrap() as f64),
//! #             String(s) => Json::String(s),
//! #             Array(a) => Json::Array(a.into_iter().map(Into::into).collect()),
//! #             Object(m) => Json::Map(
//! #                 m.into_iter()
//! #                     .map(|(k, v)| (k, v.into()))
//! #                     .collect(),
//! #             ),
//! #         }
//! #     }
//! # }
//!
//! macro_rules! json {
//!     ($( $tokens:tt )*) => {
//!         // ...
//! #         Json::from(::serde_json::json!({$($tokens)*}))
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
//!         Edit::Replace(Box::default()),      // "name"
//!         Edit::Insert,                       // "maiden name"
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
mod memoize;

pub(crate) use cost::*;
pub(crate) use fold::*;
pub(crate) use memoize::*;
