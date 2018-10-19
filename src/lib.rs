//! Create ranges in a very explicit manner
//!
//! Start with the [`from()`] function and build up a range using [`From::up_to`] or
//! [`From::down_to`].
//!
//! # Examples
//!
//! ```rust
//! extern crate a_range;
//!
//! let x = a_range::from(5).up_to(7);
//! assert_eq!(x.to_vec(), vec![5, 6, 7]);
//!
//! let x = a_range::from(3).down_to(1);
//! assert_eq!(x.to_vec(), vec![3, 2, 1]);
//! ```

#![warn(missing_docs)]

extern crate num_traits;

#[cfg(test)]
#[macro_use] extern crate proptest;

use num_traits::{Bounded, One};
use std::iter::FromIterator;
use std::ops::{AddAssign, SubAssign};

/// Start constructing a new [Range].
///
/// # Examples
///
/// ```rust
/// extern crate a_range;
///
/// let start = a_range::from(42);
/// let range = start.up_to(48);
///
/// assert_eq!(range.to_vec(), vec![42, 43, 44, 45, 46, 47, 48]);
/// ```
pub fn from<Idx>(i: Idx) -> From<Idx> {
    From { from: i }
}

/// Constructed using [`from()`]
///
/// The the methods provided for this type to build a [Range].
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd)]
pub struct From<Idx> {
    from: Idx,
}

impl<Idx> From<Idx>
where
    Idx: PartialOrd,
{
    /// Construct a [Range] that counts up to the given item.
    ///
    /// # Panics
    ///
    /// This function will panic when trying to create a [Range] where the upper bound is less than the lower bound.
    pub fn up_to(self, x: Idx) -> Range<Idx, Upwards> {
        if self.from > x {
            panic!("Invalid range: upper bound cannot be lesser than lower bound!");
        }

        Range {
            from: self.from,
            to: x,
            direction: Upwards,
        }
    }

    /// Construct a [Range] that counts down to the given item.
    ///
    /// # Panics
    ///
    /// This function will panic when trying to create a [Range] where the lower bound is less than the upper bound.
    pub fn down_to(self, x: Idx) -> Range<Idx, Downwards> {
        if self.from < x {
            panic!("Invalid range: lower bound cannot be lesser than upper bound!");
        }

        Range {
            from: self.from,
            to: x,
            direction: Downwards,
        }
    }
}

impl<Idx> From<Idx>
where
    Idx: Bounded,
{
    /// Construct a [Range] that counts up to `Idx`'s maximum value.
    ///
    /// ```rust
    /// extern crate a_range;
    ///
    /// let range = a_range::from(10).up_to_infinity();
    ///
    /// let v: Vec<i32> = range.into_iter().take(5).collect::<Vec<i32>>();
    /// assert_eq!(v, vec![10, 11, 12, 13, 14]);
    /// ```
    pub fn up_to_infinity(self) -> Range<Idx, Upwards> {
        Range {
            from: self.from,
            to: Idx::max_value(),
            direction: Upwards,
        }
    }
}

/// A range
///
/// This is basically a start, and end, an a direction.
///
/// The index type can be any type, but to get a useful range, you need to supply something that
/// implements some common traits, like [`Clone`], and [`PartialEq`]; but also [`One`] (the identity
/// element used) as well as [`AddAssign`] and [`SubAssign`] (to work increment/decrement the index).
///
/// # Note
///
/// This is generic over the index. The type parameter for the direction is an implementation
/// detail to ensure this is a type-level constant (instead of it being checked at runtime).
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd)]
pub struct Range<Idx, Direction> {
    direction: Direction,
    from: Idx,
    to: Idx,
}

#[doc(hidden)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd)]
pub struct Upwards;

#[doc(hidden)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd)]
pub struct Downwards;

/// Range counting up
impl<Idx> Range<Idx, Upwards>
where
    Idx: Clone + PartialEq + One + AddAssign + SubAssign,
{
    /// Collect range into a container
    ///
    /// Works for any container type that implements [`FromIterator`].
    pub fn collect<B>(self) -> B
    where
        B: FromIterator<Idx>,
    {
        self.into_iter().collect()
    }

    /// Turn range into a [Vec]
    pub fn to_vec(&self) -> Vec<Idx> {
        self.clone().into_iter().collect()
    }
}

/// Range counting down
impl<Idx> Range<Idx, Downwards>
where
    Idx: Clone + PartialEq + One + AddAssign + SubAssign,
{
    /// Collect range into a container
    ///
    /// Works for any container type that implements [`FromIterator`].
    pub fn collect<B>(self) -> B
    where
        B: FromIterator<Idx>,
    {
        self.into_iter().collect()
    }

    /// Turn range into a [Vec]
    pub fn to_vec(&self) -> Vec<Idx> {
        self.clone().into_iter().collect()
    }
}

impl<Idx> IntoIterator for Range<Idx, Upwards>
where
    Idx: Clone + PartialEq + One + AddAssign + SubAssign,
{
    type Item = Idx;
    type IntoIter = RangeIter<Idx, Upwards>;

    fn into_iter(self) -> Self::IntoIter {
        RangeIter {
            current: self.from,
            limit: self.to,
            direction: self.direction,
            init: false,
        }
    }
}

impl<Idx> IntoIterator for Range<Idx, Downwards>
where
    Idx: Clone + PartialEq + One + AddAssign + SubAssign,
{
    type Item = Idx;
    type IntoIter = RangeIter<Idx, Downwards>;

    fn into_iter(self) -> Self::IntoIter {
        RangeIter {
            current: self.from,
            limit: self.to,
            direction: self.direction,
            init: false,
        }
    }
}

/// Conversions to [`std::ops::Range`]
impl<Idx> Range<Idx, Upwards>
where
    Idx: Clone + One + AddAssign,
{
    /// Turn range into a [`std::ops::Range`]
    pub fn as_std_range(&self) -> std::ops::Range<Idx> {
        // std::ops::Range upper bounds are excluded, so add one
        let mut to = self.to.clone();
        to += Idx::one();

        self.from.clone()..to
    }
}

/// Conversions to [`std::ops::Range`]
impl<Idx> Into<std::ops::Range<Idx>> for Range<Idx, Upwards>
where
    Idx: Clone + One + AddAssign,
{
    fn into(self) -> std::ops::Range<Idx> {
        self.as_std_range()
    }
}

/// Conversions to [`std::ops::RangeInclusive`]
impl<Idx> Range<Idx, Upwards>
where
    Idx: Clone,
{
    /// Turn range into a [`std::ops::RangeInclusive`]
    pub fn as_std_range_inclusive(&self) -> std::ops::RangeInclusive<Idx> {
        self.from.clone()..=self.to.clone()
    }
}

/// Conversions to [`std::ops::RangeInclusive`]
impl<Idx> Into<std::ops::RangeInclusive<Idx>> for Range<Idx, Upwards>
where
    Idx: Clone,
{
    fn into(self) -> std::ops::RangeInclusive<Idx> {
        self.as_std_range_inclusive()
    }
}

/// Iterator over a range
///
/// Construct this by calling `into_iter()` on a [`Range`].
///
/// # Note
///
/// This is generic over the index. The type parameter for the direction is an implementation
/// detail to ensure this is a type-level constant (instead of it being checked at runtime).
pub struct RangeIter<Idx, Direction> {
    current: Idx,
    limit: Idx,
    #[allow(unused)]
    direction: Direction,
    init: bool,
}

/// Iterate over a reverse range
///
/// # Examples
///
/// ```rust
/// extern crate a_range;
///
/// let x = a_range::from(1).up_to(3);
/// let mut iter = x.into_iter();
///
/// // Each call to `next()` gives us the next number in the range:
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(3));
///
/// // Until the range is done
/// assert_eq!(iter.next(), None);
/// ```
impl<Idx> Iterator for RangeIter<Idx, Upwards>
where
    Idx: Clone + PartialEq + One + AddAssign + SubAssign,
{
    type Item = Idx;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.init {
            self.init = true;

            return Some(self.current.clone());
        }

        if self.current == self.limit {
            return None;
        }

        self.current += Idx::one();

        Some(self.current.clone())
    }
}

/// Iterate over a reverse range
///
/// # Examples
///
/// ```rust
/// extern crate a_range;
///
/// let x = a_range::from(3).down_to(1);
/// let mut iter = x.into_iter();
///
/// // Each call to `next()` gives us the next number in the range:
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(1));
///
/// // Until the range is done
/// assert_eq!(iter.next(), None);
/// ```
impl<Idx> Iterator for RangeIter<Idx, Downwards>
where
    Idx: Clone + PartialEq + One + AddAssign + SubAssign,
{
    type Item = Idx;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.init {
            self.init = true;

            return Some(self.current.clone());
        }

        if self.current == self.limit {
            return None;
        }

        self.current -= Idx::one();

        Some(self.current.clone())
    }
}

#[test]
fn range_collect() {
    let x: Vec<i32> = from(10).up_to(14).into_iter().take(10).collect();
    assert_eq!(x, vec![10, 11, 12, 13, 14]);
}

#[test]
fn rev_range_collect() {
    let x: Vec<i32> = from(14).down_to(10).into_iter().take(10).collect();
    assert_eq!(x, vec![14, 13, 12, 11, 10]);
}

#[test]
fn as_std_range() {
    let r = from(10).up_to(14);

    let u: Vec<i32> = r.as_std_range().into_iter().take(10).collect();
    let v: Vec<i32> = r.into_iter().take(10).collect();

    assert_eq!(u, vec![10, 11, 12, 13, 14]);
    assert_eq!(v, vec![10, 11, 12, 13, 14]);
}

#[test]
fn as_std_range_inclusive() {
    let r = from(10).up_to(14);

    let u: Vec<i32> = r.as_std_range_inclusive().into_iter().take(10).collect();
    let v: Vec<i32> = r.into_iter().take(10).collect();

    assert_eq!(u, vec![10, 11, 12, 13, 14]);
    assert_eq!(v, vec![10, 11, 12, 13, 14]);
}

#[test]
#[should_panic]
fn fail_up_to_invalid_range() {
    from(40).up_to(39);
}

#[test]
#[should_panic]
fn fail_down_to_invalid_range() {
    from(40).down_to(41);
}

#[test]
fn up_to_equivalent_val() {
    let r = from(10).up_to(10);

    assert_eq!(r.to_vec(), vec![10]);
}

#[test]
fn down_to_equivalent_val() {
    let r = from(10).down_to(10);

    assert_eq!(r.to_vec(), vec![10]);
}

#[cfg(test)]
proptest! {
    #[test]
    fn proptest_as_std_range(beg in 0u8..255, end in 0u8..255) { // 255 to prevent overflow
        prop_assume!(beg <= end);

        let r = from(beg).up_to(end);

        let u: Vec<_> = r.as_std_range().collect();
        let v: Vec<_> = r.into_iter().collect();

        prop_assert_eq!(u, v);
    }

    #[test]
    fn proptest_as_std_range_inclusive(beg in 0u8.., end in 0u8..) {
        prop_assume!(beg <= end);

        let r = from(beg).up_to(end);

        let u: Vec<_> = r.as_std_range_inclusive().collect();
        let v: Vec<_> = r.into_iter().collect();

        prop_assert_eq!(u, v);
    }

    #[test]
    fn up_to_iter_length(beg in 0usize..10000, end in 0usize..10000) {
        prop_assume!(beg <= end);

        let range = from(beg).up_to(end);
        prop_assert_eq!(range.into_iter().count(), end - beg + 1);
    }

    #[test]
    fn down_to_iter_length(beg in 0usize..10000, end in 0usize..10000) {
        prop_assume!(beg >= end);

        let range = from(beg).down_to(end);
        prop_assert_eq!(range.into_iter().count(), beg - end + 1);
    }
}
