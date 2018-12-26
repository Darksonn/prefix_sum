//! Types for slices of a `PrefixSum`.
//!
//! The types in this module allow range modifications to a `PrefixSum`, and are obtained
//! through the [`IndexMut`] trait.
//!
//! # Example
//!
//! ```
//! use prefix_sum::PrefixSum;
//!
//! let mut sum = PrefixSum::new(6);
//! sum[2..5] += 2;
//! sum[ .. ] += 3;
//!
//! sum[ ..3] -= 1;
//! sum[1.. ] += -1;
//!
//! assert_eq!(vec![2, 1, 3, 4, 4, 2], sum.build());
//! ```
//!
//! [`IndexMut`]: https://doc.rust-lang.org/std/ops/trait.IndexMut.html

use std::ops::{AddAssign, Index, IndexMut, SubAssign};
use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use crate::summable::{Summable, SummableSigned};
use crate::PrefixSum;

/// A closed range into a `PrefixSum`.
///
/// # Example
///
/// ```
/// use prefix_sum::PrefixSum;
///
/// let mut sum = PrefixSum::new(6);
/// sum[2..4] += 2;
/// sum[1..3] += 3;
/// sum[0] += 10;
///
/// assert_eq!(vec![10, 3, 5, 2, 0, 0], sum.build());
/// ```
#[repr(transparent)]
pub struct PrefixSumRange<T>([T]);

/// A range into a `PrefixSum` with no upper bound.
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
/// // The unbounded sums apply to values added with resize too.
/// sum.resize(4);
///
/// assert_eq!(vec![2, 5, 6, 5], sum.build());
/// ```
#[repr(transparent)]
pub struct UnboundedPrefixSumRange<T>(T);

impl<T: Summable> AddAssign<T> for PrefixSumRange<T> {
    #[inline]
    fn add_assign(&mut self, val: T) {
        self.0[0].add_assign_ref(&val);
        self.0[self.0.len() - 1].sub_assign(val);
    }
}
impl<T: SummableSigned> SubAssign<T> for PrefixSumRange<T> {
    #[inline]
    fn sub_assign(&mut self, val: T) {
        self.0[0].sub_assign_ref(&val);
        self.0[self.0.len() - 1].add_assign(val);
    }
}
impl<T: Summable> AddAssign<T> for UnboundedPrefixSumRange<T> {
    #[inline]
    fn add_assign(&mut self, val: T) {
        self.0.add_assign(val);
    }
}
impl<T: SummableSigned> SubAssign<T> for UnboundedPrefixSumRange<T> {
    #[inline]
    fn sub_assign(&mut self, val: T) {
        self.0.sub_assign(val);
    }
}

impl<T: Summable> Index<Range<usize>> for PrefixSum<T> {
    type Output = PrefixSumRange<T>;
    #[inline]
    fn index(&self, i: Range<usize>) -> &PrefixSumRange<T> {
        let slice = &self.values[i.start..=i.end];
        unsafe {
            // This is safe since PrefixSumRange has #[repr(transparent)]
            &*(slice as *const [T] as *const PrefixSumRange<_>)
        }
    }
}
impl<T: Summable> IndexMut<Range<usize>> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, i: Range<usize>) -> &mut PrefixSumRange<T> {
        let slice = &mut self.values[i.start..=i.end];
        unsafe {
            // This is safe since PrefixSumRange has #[repr(transparent)]
            &mut *(slice as *mut [T] as *mut PrefixSumRange<_>)
        }
    }
}

impl<T: Summable> Index<usize> for PrefixSum<T> {
    type Output = PrefixSumRange<T>;
    #[inline]
    fn index(&self, i: usize) -> &PrefixSumRange<T> {
        self.index(i..=i)
    }
}
impl<T: Summable> IndexMut<usize> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut PrefixSumRange<T> {
        self.index_mut(i..=i)
    }
}

impl<T: Summable> Index<RangeInclusive<usize>> for PrefixSum<T> {
    type Output = PrefixSumRange<T>;
    #[inline]
    fn index(&self, i: RangeInclusive<usize>) -> &PrefixSumRange<T> {
        self.index(*i.start()..(*i.end() + 1))
    }
}
impl<T: Summable> IndexMut<RangeInclusive<usize>> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, i: RangeInclusive<usize>) -> &mut PrefixSumRange<T> {
        self.index_mut(*i.start()..(*i.end() + 1))
    }
}

impl<T: Summable> Index<RangeTo<usize>> for PrefixSum<T> {
    type Output = PrefixSumRange<T>;
    #[inline]
    fn index(&self, i: RangeTo<usize>) -> &PrefixSumRange<T> {
        self.index(0..i.end)
    }
}
impl<T: Summable> IndexMut<RangeTo<usize>> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, i: RangeTo<usize>) -> &mut PrefixSumRange<T> {
        self.index_mut(0..i.end)
    }
}

impl<T: Summable> Index<RangeToInclusive<usize>> for PrefixSum<T> {
    type Output = PrefixSumRange<T>;
    #[inline]
    fn index(&self, i: RangeToInclusive<usize>) -> &PrefixSumRange<T> {
        self.index(0..=i.end)
    }
}
impl<T: Summable> IndexMut<RangeToInclusive<usize>> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, i: RangeToInclusive<usize>) -> &mut PrefixSumRange<T> {
        self.index_mut(0..=i.end)
    }
}

impl<T: Summable> Index<RangeFrom<usize>> for PrefixSum<T> {
    type Output = UnboundedPrefixSumRange<T>;
    #[inline]
    fn index(&self, i: RangeFrom<usize>) -> &UnboundedPrefixSumRange<T> {
        let reference = &self.values[i.start];
        unsafe {
            // This is safe since PrefixSumRange has #[repr(transparent)]
            &*(reference as *const T as *const UnboundedPrefixSumRange<_>)
        }
    }
}
impl<T: Summable> IndexMut<RangeFrom<usize>> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, i: RangeFrom<usize>) -> &mut UnboundedPrefixSumRange<T> {
        let reference = &mut self.values[i.start];
        unsafe {
            // This is safe since PrefixSumRange has #[repr(transparent)]
            &mut *(reference as *mut T as *mut UnboundedPrefixSumRange<_>)
        }
    }
}

impl<T: Summable> Index<RangeFull> for PrefixSum<T> {
    type Output = UnboundedPrefixSumRange<T>;
    #[inline]
    fn index(&self, _i: RangeFull) -> &UnboundedPrefixSumRange<T> {
        self.index(0..)
    }
}
impl<T: Summable> IndexMut<RangeFull> for PrefixSum<T> {
    #[inline]
    fn index_mut(&mut self, _i: RangeFull) -> &mut UnboundedPrefixSumRange<T> {
        self.index_mut(0..)
    }
}
