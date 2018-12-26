//! Traits for types that can be used in a `PrefixSum`.
//!
//! This crate has the features `num-bigint`, `num-rational` and `num-complex`, which can
//! be enabled to add implementations of `Summable` to those types. There is also a `num`
//! feature, which enables all the numeric features.

/// Trait for types that can be used in a `PrefixSum`.
///
/// The distinction between `add_assign` and `add_assign_ref` exists to allow types such
/// as [`BigInt`] to make proper use of memory allocations as appropriate.
///
/// See also the [`SummableSigned`] marker trait.
///
/// # Laws
///
///  1. Any piece of code using [`add_assign`] should be equivalent to the code using
///     [`add_assign_ref`] instead, excluding any performance differences. The same must
///     be true for [`sub_assign`] and [`sub_assign_ref`].
///  2. Addition should be [associative][1], that is if `a`, `b` and `c` are values of a
///     type implementing `Summable`, then
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     # let b: i32 = 91;
///     # let c: i32 = 31;
///     a.add_assign(b);
///     a.add_assign(c);
///     # assert_eq!(a, 80+b+c);
///     ```
///     must leave `a` in the same state as
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     # let mut b: i32 = 91;
///     # let c: i32 = 31;
///     b.add_assign(c);
///     a.add_assign(b);
///     # assert_eq!(a, 80+91+c);
///     ```
///  3. Addition should be [commutative][2], that is if `a` and `b` are values of a type
///     implementing `Summable`, then
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     # let b: i32 = 91;
///     a.add_assign(b);
///     # assert_eq!(a, 80+91);
///     ```
///     should leave `a` in the same state as what the following code leaves `b` in:
///     ```
///     # use prefix_sum::summable::Summable;
///     # let a: i32 = 80;
///     # let mut b: i32 = 91;
///     b.add_assign(a);
///     # assert_eq!(b, 80+91);
///     ```
///  4. The additive identity of [`add_assign`] should be the value returned by [`zero`],
///     that is, if `a` is a value of a type implementing `Summable`, then
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     a.add_assign(Summable::zero());
///     # assert_eq!(a, 80);
///     ```
///     must not change the value of `a`.
///  5. Any value substracted from itself must be zero, that is, if `a` and `b` are two
///     values of a type implementing `Summable`, then if `a` is equal to `b`, then
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     # let b: i32 = a;
///     a.sub_assign(b);
///     # assert_eq!(a, 0);
///     ```
///     must leave `a` in the same state as
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     a = Summable::zero();
///     # assert_eq!(a, 0);
///     ```
///  6. Subtraction should be equivalent to addition of inverses, that is if `a` and `b`
///     are values of any type implementing `Summable`, then
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     # let mut b: i32 = 91;
///     a.sub_assign(b);
///     # assert_eq!(a, 80 - 91);
///     ```
///     must leave `a` in the same state as
///     ```
///     # use prefix_sum::summable::Summable;
///     # let mut a: i32 = 80;
///     # let mut b: i32 = 91;
///     let b_tmp = b;
///     b = Summable::zero();
///     b.sub_assign(b_tmp);
///     a.add_assign(b);
///     # assert_eq!(a, 80 - 91);
///     ```
///
/// Note that usage of a `PrefixSum` will always result in negative values somewhere, so
/// unsigned integers must implement addition and subtraction in a wrapping manner to be
/// usable.
///
/// [`BigInt`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigInt.html
/// [`SummableSigned`]: trait.SummableSigned.html
/// [`zero`]: trait.Summable.html#tymethod.zero
/// [`add_assign`]: trait.Summable.html#tymethod.add_assign
/// [`add_assign_ref`]: trait.Summable.html#tymethod.add_assign_ref
/// [`sub_assign`]: trait.Summable.html#tymethod.sub_assign
/// [`sub_assign_ref`]: trait.Summable.html#tymethod.sub_assign_ref
/// [1]: https://en.wikipedia.org/wiki/Associative_property
/// [2]: https://en.wikipedia.org/wiki/Commutative_property
pub trait Summable {
    /// Returns the identity for the given type. This should always return the same value.
    fn zero() -> Self;
    /// Add the given value to self.
    fn add_assign_ref(&mut self, rhs: &Self);
    /// Subtract the given value from self.
    fn sub_assign_ref(&mut self, rhs: &Self);
    /// Add the given value to self while reusing resources in `rhs`.
    fn add_assign(&mut self, rhs: Self);
    /// Subtract the given value from self while reusing resources in `rhs`.
    fn sub_assign(&mut self, rhs: Self);
}

/// A marker trait on types that allow negative values.
///
/// Types without this marker cannot use `sum[a..b] -= value;`.
pub trait SummableSigned: Summable {}

#[cfg(feature = "num-bigint")]
impl Summable for num_bigint::BigInt {
    fn zero() -> Self {
        0u32.into()
    }
    fn add_assign_ref(&mut self, rhs: &Self) {
        *self += rhs;
    }
    fn sub_assign_ref(&mut self, rhs: &Self) {
        *self -= rhs;
    }
    fn add_assign(&mut self, rhs: Self) {
        *self += rhs;
    }
    fn sub_assign(&mut self, rhs: Self) {
        *self -= rhs;
    }
}
macro_rules! impl_summable_ratio {
    ( $ty:ty, $zero:expr ) => {
        #[cfg(feature = "num-rational")]
        impl SummableSigned for num_rational::Ratio<$ty> {}
        #[cfg(feature = "num-rational")]
        impl Summable for num_rational::Ratio<$ty> {
            #[inline]
            fn zero() -> Self {
                $zero
            }
            #[inline]
            fn add_assign_ref(&mut self, rhs: &Self) {
                *self += rhs;
            }
            #[inline]
            fn sub_assign_ref(&mut self, rhs: &Self) {
                *self -= rhs;
            }
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                *self += rhs;
            }
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                *self -= rhs;
            }
        }
    };
}
impl_summable_ratio!(i8, 0.into());
impl_summable_ratio!(i16, 0.into());
impl_summable_ratio!(i32, 0.into());
impl_summable_ratio!(i64, 0.into());
impl_summable_ratio!(i128, 0.into());
impl_summable_ratio!(isize, 0.into());
#[cfg(feature = "num-bigint")]
impl_summable_ratio!(num_bigint::BigInt, num_bigint::BigInt::from(0).into());

#[cfg(feature = "num-complex")]
impl<T: SummableSigned> SummableSigned for num_complex::Complex<T> {}
#[cfg(feature = "num-complex")]
impl<T: SummableSigned> Summable for num_complex::Complex<T> {
    #[inline]
    fn zero() -> Self {
        num_complex::Complex {
            re: T::zero(),
            im: T::zero(),
        }
    }
    #[inline]
    fn add_assign_ref(&mut self, rhs: &Self) {
        T::add_assign_ref(&mut self.re, &rhs.re);
        T::add_assign_ref(&mut self.im, &rhs.im);
    }
    #[inline]
    fn sub_assign_ref(&mut self, rhs: &Self) {
        T::sub_assign_ref(&mut self.re, &rhs.re);
        T::sub_assign_ref(&mut self.im, &rhs.im);
    }
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        T::add_assign(&mut self.re, rhs.re);
        T::add_assign(&mut self.im, rhs.im);
    }
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        T::sub_assign(&mut self.re, rhs.re);
        T::sub_assign(&mut self.im, rhs.im);
    }
}

macro_rules! impl_summable_signed {
    ( $ty:tt ) => {
        impl SummableSigned for $ty {}
        impl Summable for $ty {
            #[inline]
            fn zero() -> $ty {
                0 as $ty
            }
            #[inline]
            fn add_assign_ref(&mut self, rhs: &$ty) {
                *self += *rhs;
            }
            #[inline]
            fn sub_assign_ref(&mut self, rhs: &$ty) {
                *self -= *rhs;
            }
            #[inline]
            fn add_assign(&mut self, rhs: $ty) {
                *self += rhs;
            }
            #[inline]
            fn sub_assign(&mut self, rhs: $ty) {
                *self -= rhs;
            }
        }
    };
}
macro_rules! impl_summable_signed_wrapping {
    ( $ty:tt ) => {
        impl SummableSigned for std::num::Wrapping<$ty> {}
        impl Summable for std::num::Wrapping<$ty> {
            #[inline]
            fn zero() -> Self {
                std::num::Wrapping(0 as $ty)
            }
            #[inline]
            fn add_assign_ref(&mut self, rhs: &Self) {
                *self += *rhs;
            }
            #[inline]
            fn sub_assign_ref(&mut self, rhs: &Self) {
                *self -= *rhs;
            }
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                *self += rhs;
            }
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                *self -= rhs;
            }
        }
    };
}
macro_rules! impl_summable_unsigned {
    ( $ty:tt ) => {
        impl Summable for $ty {
            #[inline]
            fn zero() -> $ty {
                0 as $ty
            }
            #[inline]
            fn add_assign_ref(&mut self, rhs: &$ty) {
                *self = self.wrapping_add(*rhs);
            }
            #[inline]
            fn sub_assign_ref(&mut self, rhs: &$ty) {
                *self = self.wrapping_sub(*rhs);
            }
            #[inline]
            fn add_assign(&mut self, rhs: $ty) {
                *self = self.wrapping_add(rhs);
            }
            #[inline]
            fn sub_assign(&mut self, rhs: $ty) {
                *self = self.wrapping_sub(rhs);
            }
        }
    };
}
macro_rules! impl_summable_unsigned_wrapping {
    ( $ty:tt ) => {
        impl Summable for std::num::Wrapping<$ty> {
            #[inline]
            fn zero() -> Self {
                std::num::Wrapping(0 as $ty)
            }
            #[inline]
            fn add_assign_ref(&mut self, rhs: &Self) {
                *self += rhs;
            }
            #[inline]
            fn sub_assign_ref(&mut self, rhs: &Self) {
                *self -= *rhs;
            }
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                *self += rhs;
            }
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                *self -= rhs;
            }
        }
        impl SummableSigned for std::num::Wrapping<$ty> {}
    };
}

impl_summable_signed!(i8);
impl_summable_signed!(i16);
impl_summable_signed!(i32);
impl_summable_signed!(i64);
impl_summable_signed!(i128);
impl_summable_signed!(isize);
impl_summable_signed!(f32);
impl_summable_signed!(f64);
impl_summable_unsigned!(u8);
impl_summable_unsigned!(u16);
impl_summable_unsigned!(u32);
impl_summable_unsigned!(u64);
impl_summable_unsigned!(u128);
impl_summable_unsigned!(usize);
impl_summable_signed_wrapping!(i8);
impl_summable_signed_wrapping!(i16);
impl_summable_signed_wrapping!(i32);
impl_summable_signed_wrapping!(i64);
impl_summable_signed_wrapping!(i128);
impl_summable_signed_wrapping!(isize);
impl_summable_unsigned_wrapping!(u8);
impl_summable_unsigned_wrapping!(u16);
impl_summable_unsigned_wrapping!(u32);
impl_summable_unsigned_wrapping!(u64);
impl_summable_unsigned_wrapping!(u128);
impl_summable_unsigned_wrapping!(usize);
