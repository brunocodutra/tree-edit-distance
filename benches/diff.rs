use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use itertools::Itertools;
use tree_edit_distance::{diff, Node, Tree};

#[derive(Default, Clone)]
struct TreeNode {
    children: Vec<Self>,
}

impl<'n> Node<'n> for TreeNode {
    type Kind = ();
    fn kind(&'n self) -> Self::Kind {}

    type Weight = usize;
    fn weight(&'n self) -> Self::Weight {
        1
    }
}

impl<'t> Tree<'t> for TreeNode {
    type Child = Self;
    type Children = &'t [Self];
    fn children(&'t self) -> Self::Children {
        &self.children
    }
}

fn tree(leaves: Vec<TreeNode>, r: usize) -> TreeNode {
    if leaves.len() < r {
        TreeNode { children: leaves }
    } else {
        let n = (leaves.len() + r - 1) / r;
        TreeNode {
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
            &tree(vec![TreeNode::default(); 100], r),
            |b, t| b.iter(|| diff(t, t)),
        );
    }
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
