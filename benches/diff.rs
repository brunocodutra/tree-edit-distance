use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use itertools::Itertools;
use tree_edit_distance::{diff, Node};

#[derive(Default, Clone)]
struct Tree {
    children: Vec<Self>,
}

impl<'n> Node<'n> for Tree {
    type Kind = ();
    fn kind(&'n self) -> Self::Kind {}

    type Weight = usize;
    fn weight(&'n self) -> Self::Weight {
        1
    }

    type Child = Self;
    type Children = &'n [Self];
    fn children(&'n self) -> Self::Children {
        &self.children
    }
}

fn tree(leaves: Vec<Tree>, r: usize) -> Tree {
    if leaves.len() < r {
        Tree { children: leaves }
    } else {
        let n = (leaves.len() + r - 1) / r;
        Tree {
            children: leaves
                .into_iter()
                .chunks(n)
                .into_iter()
                .map(|c| tree(c.collect(), r))
                .collect(),
        }
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
