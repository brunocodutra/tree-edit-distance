use std::ops::Add;

pub(crate) trait Cost {
    type Output: Default + Copy + Add<Output = Self::Output>;
    fn cost(&self) -> Self::Output;
}

impl<C: Cost<Output = V>, V: Default + Copy + Add<Output = V>> Cost for [C] {
    type Output = C::Output;
    fn cost(&self) -> Self::Output {
        self.iter().map(C::cost).reduce(V::add).unwrap_or_default()
    }
}

impl<V: Default + Copy + Add<Output = V>> Cost for V {
    type Output = V;

    #[inline]
    fn cost(&self) -> Self::Output {
        *self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::{vec, SizeRange};
    use test_strategy::proptest;

    #[proptest]
    fn cost_of_slice_equals_sum_of_costs(
        #[strategy(vec(..32u32, SizeRange::default()))] s: Vec<u32>,
    ) {
        assert_eq!(s.cost(), s.iter().sum::<u32>());
    }
}
