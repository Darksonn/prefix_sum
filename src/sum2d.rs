//! Prefix sums, but in two dimensions.
//!
//! # Example
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

use crate::summable::{Summable, SummableSigned};
use std::ops::{Index, IndexMut};

/// A prefix sum in two dimensional space.
///
/// # Example
///
/// ```
/// use prefix_sum::sum2d::{PrefixSum2D, Rect};
///
/// let mut sum = PrefixSum2D::new(4, 4);
/// sum.add_rectangle(Rect::new(1, 1, 2, 2), 2);
/// sum.add_rectangle(Rect::new(0, 0, 2, 2), 2);
/// sum.add_rectangle(Rect::new(0, 2, 1, 2), 8);
///
/// assert_eq!(sum.build().into_vec(), vec![
///     2, 2, 0, 0,
///     2, 4, 2, 0,
///     8, 2, 2, 0,
///     8, 0, 0, 0,
/// ]);
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PrefixSum2D<T> {
    inner: Vec<T>,
    width: usize,
}
/// A rectangle.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Rect {
    /// The x-coordinate of a corner of the rectangle.
    pub x: usize,
    /// The y-coordinate of a corner of the rectangle.
    pub y: usize,
    /// The width of the rectangle.
    pub w: usize,
    /// The height of the rectangle.
    pub h: usize,
}
impl Rect {
    /// Create a new `Rect`.
    #[inline]
    pub fn new(x: usize, y: usize, w: usize, h: usize) -> Self {
        Rect { x, y, w, h }
    }
    /// Returns `self.x + self.w - 1`.
    #[inline]
    pub fn x2(&self) -> usize {
        self.x + self.w - 1
    }
    /// Returns `self.y + self.h - 1`.
    #[inline]
    pub fn y2(&self) -> usize {
        self.y + self.h - 1
    }
}

impl<T: Summable> PrefixSum2D<T> {
    /// Create a new prefix sum where all values are zero.
    ///
    /// This is `O(width*height)`.
    pub fn new(width: usize, height: usize) -> Self {
        let mut vec = Vec::with_capacity(width * height);
        for _ in 0..width * height {
            vec.push(T::zero());
        }
        PrefixSum2D { inner: vec, width }
    }

    /// Add the given value to every spot in the given rectangle.
    /// This is a constant time operation.
    pub fn add_rectangle(&mut self, rect: Rect, add: T) {
        let i1 = self.index(rect.x, rect.y);
        self.inner[i1].add_assign_ref(&add);

        if rect.x2() + 1 != self.width {
            let i2 = self.index(rect.x2() + 1, rect.y);
            self.inner[i2].sub_assign_ref(&add);
        }
        if rect.y2() + 1 != self.height() {
            let i3 = self.index(rect.x, rect.y2() + 1);
            self.inner[i3].sub_assign_ref(&add);

            if rect.x2() + 1 != self.width {
                let i4 = self.index(rect.x2() + 1, rect.y2() + 1);
                self.inner[i4].add_assign(add);
            }
        }
    }
    /// Subtract the given value from every spot in the given rectangle.
    /// This is a constant time operation.
    pub fn sub_rectangle(&mut self, rect: Rect, sub: T)
    where
        T: SummableSigned,
    {
        let i1 = self.index(rect.x, rect.y);
        self.inner[i1].sub_assign_ref(&sub);

        if rect.x2() + 1 != self.width {
            let i2 = self.index(rect.x2() + 1, rect.y);
            self.inner[i2].add_assign_ref(&sub);
        }
        if rect.y2() + 1 != self.height() {
            let i3 = self.index(rect.x, rect.y2() + 1);
            self.inner[i3].add_assign_ref(&sub);

            if rect.x2() + 1 != self.width {
                let i4 = self.index(rect.x2() + 1, rect.y2() + 1);
                self.inner[i4].sub_assign(sub);
            }
        }
    }

    /// The width of the rectangle.
    /// This is a constant time operation.
    #[inline]
    pub fn width(&self) -> usize {
        self.width
    }
    /// The height of the rectangle.
    /// This is a constant time operation.
    #[inline]
    pub fn height(&self) -> usize {
        self.inner.len() / self.width
    }

    #[inline(always)]
    fn index(&self, x: usize, y: usize) -> usize {
        self.width * y + x
    }
    #[inline(always)]
    fn inner_add(&mut self, i1: usize, i2: usize) {
        debug_assert!(i1 < i2);
        let (a, b) = self.inner[i1..=i2].split_at_mut(i2 - i1);
        let a = &a[0];
        let b = &mut b[0];
        Summable::add_assign_ref(b, a);
    }

    /// Create a [`Buf2D`] with the values this prefix sum represents.
    /// This is an `O(width*height)` operation.
    ///
    /// [`Buf2D`]: struct.Buf2D.html
    pub fn build(mut self) -> Buf2D<T> {
        for y in 0..self.height() {
            for x in 1..self.width() {
                self.inner_add(y * self.width + x - 1, y * self.width + x);
            }
        }
        for y in 1..self.height() {
            for x in 0..self.width() {
                self.inner_add(self.width * (y - 1) + x, self.width * y + x);
            }
        }
        Buf2D {
            inner: self.inner,
            width: self.width,
        }
    }
}

/// A two dimensional vector.
///
/// This type is mainly meant to be used as the return value of [`build`].
///
/// # Example
///
/// ```
/// use prefix_sum::sum2d::Buf2D;
///
/// let mut buf2d = Buf2D::new(2, 2, 0i32);
/// buf2d[(0,0)] = 1;
/// buf2d[(1,0)] = 2;
/// buf2d[(0,1)] = 3;
/// buf2d[(1,1)] = 4;
///
/// assert_eq!(buf2d.into_vec(), vec![1, 2, 3, 4]);
/// ```
///
/// [`build`]: struct.PrefixSum2D.html#method.build
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Buf2D<T> {
    inner: Vec<T>,
    width: usize,
}
impl<T> Buf2D<T> {
    /// Creates a new `Buf2D` with the specified size and a clone of `init` in every spot.
    /// This is `O(width*height)`.
    pub fn new(width: usize, height: usize, init: T) -> Self
    where
        T: Clone,
    {
        let mut vec = Vec::with_capacity(width * height);
        for _ in 0..width * height {
            vec.push(init.clone());
        }
        Buf2D { inner: vec, width }
    }
    /// Create a `Buf2D` with the given data.
    /// This is a constant time operation.
    ///
    /// Panics if `vec.len()` is not a multiple of `width`.
    pub fn from_vec(vec: Vec<T>, width: usize) -> Self {
        if vec.len() % width != 0 {
            panic!("Buf2D must be a rectangle.");
        }
        Buf2D { inner: vec, width }
    }
    /// Returns a vector where `(x,y)` is stored at `y*width + x`.
    /// This is a constant time operation.
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }
    /// Return the width of the `Buf2D`.
    /// This is a constant time operation.
    pub fn width(&self) -> usize {
        self.width
    }
    /// Return the height of the `Buf2D`.
    /// This is a constant time operation.
    pub fn height(&self) -> usize {
        self.inner.len() / self.width
    }
}

impl<T> Index<(usize, usize)> for Buf2D<T> {
    type Output = T;
    /// Access the item at `(x,y)` in the buffer.
    /// This is a constant time operation.
    fn index(&self, i: (usize, usize)) -> &T {
        let x = i.0;
        let y = i.1;
        &self.inner[y * self.width + x]
    }
}
impl<T> IndexMut<(usize, usize)> for Buf2D<T> {
    /// Modify the item at `(x,y)` in the buffer.
    /// This is a constant time operation.
    fn index_mut(&mut self, i: (usize, usize)) -> &mut T {
        let x = i.0;
        let y = i.1;
        &mut self.inner[y * self.width + x]
    }
}

/// An iterator over the rows in a `Buf2D`.
///
/// # Example
///
/// ```
/// use prefix_sum::sum2d::Buf2D;
///
/// let mut buf2d = Buf2D::new(2, 2, 0i32);
/// buf2d[(0,0)] = 1;
/// buf2d[(1,0)] = 2;
/// buf2d[(0,1)] = 3;
/// buf2d[(1,1)] = 4;
///
/// let mut res = Vec::new();
/// for row in &buf2d {
///     for value in row {
///         res.push(*value);
///     }
/// }
/// assert_eq!(res, vec![1, 2, 3, 4]);
/// ```
pub struct Buf2DIter<'a, T> {
    inner: &'a Vec<T>,
    width: usize,
    i: usize,
}
impl<'a, T> IntoIterator for &'a Buf2D<T> {
    type Item = std::slice::Iter<'a, T>;
    type IntoIter = Buf2DIter<'a, T>;
    fn into_iter(self) -> Buf2DIter<'a, T> {
        Buf2DIter {
            inner: &self.inner,
            width: self.width,
            i: 0,
        }
    }
}
impl<'a, T> Iterator for Buf2DIter<'a, T> {
    type Item = std::slice::Iter<'a, T>;
    fn next(&mut self) -> Option<std::slice::Iter<'a, T>> {
        if self.i < self.inner.len() {
            let next_i = self.i + self.width;
            let slice = &self.inner[self.i..next_i];
            self.i = next_i;
            Some(slice.into_iter())
        } else {
            None
        }
    }
}
