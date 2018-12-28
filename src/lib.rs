//! This crate provides the [prefix sum][1] data structure.
//!
//! A prefix sum is a data structure allowing several interval modifications to be
//! accumulated and applied to an array.
//!
//! ```
//! use prefix_sum::PrefixSum;
//!
//! let mut sum = PrefixSum::new(6);
//! // Each of these operations is O(1).
//! sum[2..4] += 2;
//! sum[1..3] += 3;
//! sum[0]    += 10;
//! sum[3..]  += 7;
//!
//! // build is O(len).
//! assert_eq!(vec![10, 3, 5, 9, 7, 7], sum.build());
//! ```
//!
//! The types usable in a [`PrefixSum`] are those implementing [`Summable`]. This trait
//! is implemented for the standard number types, and various features on the crate enable
//! implementations for various foreign types. See the [`summable`][2] module
//! documentation for a list of these features.
//!
//! Note that usage of unsigned types in a prefix sum requires wrapping subtraction and
//! addition to be usable.
//!
//! A two dimensional prefix sum is also provided in the [`sum2d`] module.
//!
//! ```
//! use prefix_sum::sum2d::{PrefixSum2D, Rect};
//!
//! let mut sum = PrefixSum2D::new(4, 4);
//! sum.add_rectangle(Rect::new(1, 1, 2, 2), 2);
//! sum.add_rectangle(Rect::new(0, 0, 2, 2), 2);
//! sum.add_rectangle(Rect::new(0, 2, 1, 2), 8);
//!
//! assert_eq!(sum.build().into_vec(), vec![
//!     2, 2, 0, 0,
//!     2, 4, 2, 0,
//!     8, 2, 2, 0,
//!     8, 0, 0, 0,
//! ]);
//! ```
//!
//!   [1]: https://en.wikipedia.org/wiki/Prefix_sum
//!   [`PrefixSum`]: struct.PrefixSum.html
//!   [`Summable`]: summable/trait.Summable.html
//!   [2]: summable/index.html
//!   [`sum2d`]: sum2d/index.html

pub mod iter;
pub mod range;
pub mod sum2d;
pub mod summable;

use crate::iter::Iter;
use crate::summable::Summable;

/// Data type allowing `O(1)` interval modifications to an array.
///
/// # Example
///
/// ```
/// use prefix_sum::PrefixSum;
///
/// let mut sum = PrefixSum::new(6);
/// sum[2..=4] += 2;
/// sum[1..3] += 3;
///
/// sum[ ..3] -= 1;
/// sum[4.. ] += 10;
///
/// assert_eq!(vec![-1, 2, 4, 2, 12, 10], sum.build());
/// ```
///
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PrefixSum<T: Summable> {
    values: Vec<T>,
}

impl<T: Summable> PrefixSum<T> {
    /// Builds a new `PrefixSum` filled with zeroes.
    ///
    /// This runs in linear time in the length.
    pub fn new(len: usize) -> PrefixSum<T> {
        let mut vec = Vec::with_capacity(len + 1);
        for _ in 0..=len {
            vec.push(T::zero());
        }
        PrefixSum { values: vec }
    }
    /// Returns a `PrefixSum`, such that calling [`build`] on the result would return the
    /// input.
    ///
    /// This allocates if `vec.len() == vec.capacity()`. This runs in linear time in the
    /// length.
    ///
    /// # Examples
    ///
    /// ```
    /// use prefix_sum::PrefixSum;
    ///
    /// let sum = PrefixSum::from_vec(vec![1, 2, 3, 4]);
    /// assert_eq!(sum.build(), vec![1, 2, 3, 4]);
    /// ```
    ///
    /// When resized, new items will be zero.
    ///
    /// ```
    /// use prefix_sum::PrefixSum;
    ///
    /// let mut sum = PrefixSum::from_vec(vec![1, 2, 3, 4]);
    /// sum.resize(5);
    /// assert_eq!(sum.build(), vec![1, 2, 3, 4, 0]);
    /// ```
    ///
    ///   [`build`]: struct.PrefixSum.html#method.build
    pub fn from_vec(mut vec: Vec<T>) -> PrefixSum<T> {
        if vec.len() == 0 {
            vec.push(T::zero());
            return PrefixSum {
                values: vec,
            };
        }
        let mut negsum = T::zero();
        negsum.sub_assign_ref(&vec[0]);
        for i in (1..vec.len()).rev() {
            let (a, b) = vec[i-1 ..= i].split_at_mut(1);
            let a = &a[0];
            let b = &mut b[0];
            Summable::sub_assign_ref(b, a);
            negsum.sub_assign_ref(&*b);
        }

        vec.push(negsum);
        PrefixSum {
            values: vec,
        }
    }
    /// Returns the number of items in this prefix sum.
    ///
    /// This runs in constant time.
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len() - 1
    }
    /// Resize the prefix sum. Any changes done using intervals with no upper bound will
    /// affect the newly created values.
    ///
    /// If the size is decreased, this is constant time. If the size is increased, this
    /// runs in amortized linear time in the number of items added.
    ///
    /// # Example
    ///
    /// ```
    /// use prefix_sum::PrefixSum;
    ///
    /// let mut sum = PrefixSum::new(3);
    /// sum[ ..] += 2;
    /// sum[1..] += 3;
    ///
    /// sum[2] += 1;
    /// assert_eq!(vec![2, 5, 6], sum.clone().build());
    ///
    /// sum.resize(4);
    ///
    /// assert_eq!(vec![2, 5, 6, 5], sum.build());
    /// ```
    pub fn resize(&mut self, len: usize) {
        self.values.reserve(len+1);
        while self.values.len() <= len {
            self.values.push(T::zero());
        }
    }
    /// Build the vector containing the computed sums. This is linear time in the length.
    pub fn build(self) -> Vec<T>
    where
        T: std::fmt::Debug,
    {
        let mut vec = self.values;

        for i in 0..vec.len() - 2 {
            let (a, b) = vec[i..=i + 1].split_at_mut(1);
            let a = &a[0];
            let b = &mut b[0];
            Summable::add_assign_ref(b, a);
        }

        vec.pop();
        vec
    }
    /// Create an iterator through the sums in this `PrefixSum`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T>
    where
        T: Clone,
    {
        self.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::PrefixSum;
    #[test]
    fn test_sum() {
        let mut sum: PrefixSum<i32> = PrefixSum::new(5);
        assert_eq!(sum.len(), 5);

        sum[3..5] += 10;
        assert_eq!(vec![0, 0, 0, 10, 10], sum.clone().build());

        sum[1..4] -= 3;
        assert_eq!(vec![0, -3, -3, 7, 10], sum.clone().build());

        sum[3..] += 5;
        assert_eq!(vec![0, -3, -3, 12, 15], sum.clone().build());

        sum.resize(6);
        assert_eq!(vec![0, -3, -3, 12, 15, 5], sum.clone().build());
    }
    #[test]
    fn test_unsigned() {
        let mut sum: PrefixSum<u32> = PrefixSum::new(5);
        assert_eq!(sum.len(), 5);

        sum[1..5] += 10;
        assert_eq!(vec![0, 10, 10, 10, 10], sum.clone().build());

        sum[1..4] += (-3i32) as u32;
        assert_eq!(vec![0, 7, 7, 7, 10], sum.clone().build());

        sum[3..] += 5;
        assert_eq!(vec![0, 7, 7, 12, 15], sum.clone().build());

        sum.resize(6);
        assert_eq!(vec![0, 7, 7, 12, 15, 5], sum.clone().build());
    }
}
