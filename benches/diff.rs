use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use derive_more::From;
use proptest::strategy::{LazyJust, ValueTree};
use proptest::{collection::vec, prelude::*, test_runner::TestRunner};
use tree_edit_distance::{diff, Node, Tree};

#[derive(Debug, From)]
struct TreeNode {
    weight: u8,
    children: Vec<Self>,
}

impl<'n> Node<'n> for TreeNode {
    type Kind = ();
    fn kind(&'n self) -> Self::Kind {}

    type Weight = u32;
    fn weight(&'n self) -> Self::Weight {
        self.weight.into()
    }
}

impl<'t> Tree<'t> for TreeNode {
    type Children = &'t [Self];
    fn children(&'t self) -> Self::Children {
        &self.children
    }
}

fn tree(depth: u32, breadth: u32) -> impl Strategy<Value = TreeNode> {
    let size = (breadth.pow(depth + 1) - 1) / (breadth - 1) / 2; // half the maximum number of nodes
    (1u8.., LazyJust::new(Vec::new))
        .prop_map_into()
        .prop_recursive(depth, size, breadth, move |inner| {
            (1u8.., vec(inner, ..=breadth as usize)).prop_map_into()
        })
}

fn bench(c: &mut Criterion) {
    let mut runner = TestRunner::default();
    let mut group = c.benchmark_group("n-ary tree diff");
    for (d, b) in [(7, 2), (3, 6), (2, 15), (1, 255)] {
        group.bench_with_input(format!("depth={}/breadth={}", d, b), &tree(d, b), |b, s| {
            b.iter_batched_ref(
                || (s, s).new_tree(&mut runner).unwrap().current(),
                |(a, b)| diff(a, b),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
