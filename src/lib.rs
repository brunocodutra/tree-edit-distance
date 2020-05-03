//! # Overview
//!
//! This crate provides an implementation of a recursive generalized version of the
//! [Levenshtein distance][levenshtein] for arbitrary sequences that finds the smallest possible
//! diff between two trees, according to a user-defined measure for the cost of inserting and
//! removing nodes. The smallest possible diff is defined by the the lowest cost sequence of edits
//! that transforms one tree into the other.
//!
//! [levenshtein]:  https://en.wikipedia.org/wiki/Levenshtein_distance

mod node;

pub use node::Node;
