use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use derive_more::{Deref, From};
use itertools::Itertools;
use tree_edit_distance::{diff, Node};

#[derive(Default, Clone, From, Deref)]
struct Tree(#[deref(forward)] Vec<Self>);

impl<'n> Node<'n> for Tree {
    type Kind = ();
    fn kind(&'n self) -> Self::Kind {}

    type Weight = usize;
    fn weight(&'n self) -> Self::Weight {
        1
    }
}

fn tree(leaves: Vec<Tree>, r: usize) -> Tree {
    if leaves.len() < r {
        leaves.into()
    } else {
        let chunks = (leaves.len() + r - 1) / r;
        leaves
            .into_iter()
            .chunks(chunks)
            .into_iter()
            .map(|c| tree(c.collect(), r))
            .collect::<Vec<_>>()
            .into()
    }
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("n-tree diff");
    for r in [4, 8, 16] {
        group.bench_with_input(
            BenchmarkId::from_parameter(r),
            &tree(vec![Tree::default(); 100], r),
            |b, t| b.iter(|| diff(t, t)),
        );
    }
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
