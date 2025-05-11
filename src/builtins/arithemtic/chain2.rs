pub struct Chain2<T, U> {
    pub inner: std::iter::Chain<T, U>,
}

impl<A, B> Iterator for Chain2<A, B>
where
    A: Iterator,
    B: Iterator<Item = A::Item>,
{
    type Item = A::Item;

    #[inline]
    fn next(&mut self) -> Option<A::Item> {
        self.inner.next()
    }

    #[inline]
    fn count(self) -> usize {
        self.inner.count()
    }

    fn fold<Acc, F>(self, acc: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        self.inner.fold(acc, f)
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.inner.nth(n)
    }

    #[inline]
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        self.inner.find(predicate)
    }

    #[inline]
    fn last(self) -> Option<A::Item> {
        self.inner.last()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<A, B> DoubleEndedIterator for Chain2<A, B>
where
    A: DoubleEndedIterator,
    B: DoubleEndedIterator<Item = A::Item>,
{
    #[inline]
    fn next_back(&mut self) -> Option<A::Item> {
        self.inner.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.inner.nth_back(n)
    }

    #[inline]
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        self.inner.rfind(predicate)
    }

    fn rfold<Acc, F>(self, acc: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        self.inner.fold(acc, f)
    }
}

impl<A, B> std::iter::FusedIterator for Chain2<A, B>
where
    A: std::iter::FusedIterator,
    B: std::iter::FusedIterator<Item = A::Item>,
{
}

impl<A: Default, B: Default> Default for Chain2<A, B> {
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}

impl<T, U> ExactSizeIterator for Chain2<T, U>
where
    T: Iterator + ExactSizeIterator,
    U: Iterator<Item = T::Item> + ExactSizeIterator,
{
}
