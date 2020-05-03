# TreeEditDistance [![crate.badge]][crate.home] [![docs.badge]][docs.home]

This crate provides an algorithm to compute the lowest cost sequence of edits between two trees.
It is based on a recursive generalized version of the [Levenshtein distance][levenshtein] for 
arbitrary sequences, where inserting/deleting nodes may have an arbitrary user-defined cost.

## Using TreeEditDistance

TreeEditDistance is available on [crates.io][crate.home], 
simply add it as a dependency in your `Cargo.toml`:

```
[dependencies]
tree-edit-distance = "0.1"
```

The full API documentation is available on [docs.rs][docs.home]

## License

TreeEditDistance is distributed under the terms of the MIT license, see [LICENSE] for details.

[crate.home]:       https://crates.io/crates/tree-edit-distance
[crate.badge]:      https://meritbadge.herokuapp.com/tree-edit-distance

[docs.home]:        https://docs.rs/tree-edit-distance
[docs.badge]:       https://docs.rs/tree-edit-distance/badge.svg

[issues]:           https://github.com/brunocodutra/tree-edit-distance/issues
[pulls]:            https://github.com/brunocodutra/tree-edit-distance/pulls

[LICENSE]:          https://github.com/brunocodutra/tree-edit-distance/blob/master/LICENSE

[levenshtein]:      https://en.wikipedia.org/wiki/Levenshtein_distance
