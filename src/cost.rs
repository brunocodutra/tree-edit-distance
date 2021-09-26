pub(crate) trait Cost {
    type Output;
    fn cost(&self) -> Self::Output;
}
