use std::ops::Add;

pub(crate) trait Fold<I: ?Sized = Self> {
    fn fold<R, Fn: FnMut(R, &I) -> R>(&self, init: R, f: &mut Fn) -> R;

    #[inline]
    fn sum<N: Default + Add<Output = N>, Fn: FnMut(&I) -> N>(&self, mut f: Fn) -> N {
        self.fold(N::default(), &mut |n, i| n + f(i))
    }

    #[inline]
    fn count(&self) -> usize {
        self.sum(|_| 1)
    }
}

impl<F: Fold<I>, I: ?Sized> Fold<I> for [F] {
    fn fold<R, Fn: FnMut(R, &I) -> R>(&self, init: R, f: &mut Fn) -> R {
        self.iter().fold(init, |r, i| i.fold(r, f))
    }
}
