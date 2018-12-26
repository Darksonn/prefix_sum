//! Iterators over `PrefixSum`.
//!
//! # Example
//!
//! ```
//! use prefix_sum::PrefixSum;
//!
//! let mut sum = PrefixSum::new(4);
//! sum[1..=2] += 2;
//!
//! let mut iter = sum.iter();
//! assert_eq!(iter.next(), Some(0));
//! assert_eq!(iter.next(), Some(2));
//! assert_eq!(iter.next(), Some(2));
//! assert_eq!(iter.next(), Some(0));
//! assert_eq!(iter.next(), None);
//! ```

use crate::{PrefixSum, Summable};

/// An iterator through a `PrefixSum` that clones each return value.
///
/// # Example
///
/// ```
/// use prefix_sum::PrefixSum;
///
/// let mut sum = PrefixSum::new(4);
/// sum[1..=2] += 3;
/// sum[2..] += 1;
///
/// let mut iter = sum.iter();
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next(), Some(4));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<'a, T: Summable + Clone> {
    sum: T,
    inner: std::slice::Iter<'a, T>,
}
impl<'a, T: Summable + Clone> Iterator for Iter<'a, T> {
    type Item = T;
    #[inline]
    fn next(&mut self) -> Option<T> {
        match self.inner.next() {
            None => None,
            Some(value) => {
                self.sum.add_assign_ref(value);
                Some(self.sum.clone())
            }
        }
    }
}
impl<'a, T: Summable + Clone> IntoIterator for &'a PrefixSum<T> {
    type IntoIter = Iter<'a, T>;
    type Item = T;
    #[inline]
    fn into_iter(self) -> Iter<'a, T> {
        Iter {
            sum: T::zero(),
            inner: self.values[..self.values.len() - 1].iter(),
        }
    }
}

/// An iterator through a `PrefixSum`.
///
/// # Example
///
/// ```
/// use prefix_sum::PrefixSum;
///
/// let mut sum = PrefixSum::new(4);
/// sum[1..=2] += 3;
/// sum[2..] += 1;
///
/// let mut iter = sum.into_iter();
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next(), Some(4));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), None);
/// ```
pub struct IntoIter<T: Summable> {
    sum: T,
    inner: std::vec::IntoIter<T>,
}
impl<T: Summable> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self.inner.next() {
            None => None,
            Some(mut next) => {
                next.add_assign_ref(&self.sum);
                Some(std::mem::replace(&mut self.sum, next))
            }
        }
    }
}
impl<T: Summable> IntoIterator for PrefixSum<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        let mut iter = self.values.into_iter();
        match iter.next() {
            None => IntoIter {
                sum: T::zero(),
                inner: iter,
            },
            Some(sum) => IntoIter { inner: iter, sum },
        }
    }
}
