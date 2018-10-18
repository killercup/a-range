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

use num_traits::One;
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

impl<Idx> From<Idx> {
    /// Construct a [Range] that counts up to the given item.
    pub fn up_to(self, x: Idx) -> Range<Idx, Upwards> {
        Range {
            from: self.from,
            to: x,
            direction: Upwards
        }
    }

    /// Construct a [Range] that counts down to the given item.
    pub fn down_to(self, x: Idx) -> Range<Idx, Downwards> {
        Range {
            from: self.from,
            to: x,
            direction: Downwards,
        }
    }
}

/// A range
///
/// This is basically a start, and end, an a direction.
///
/// The index type can be any type, but to get a useful range, you need to supply something that
/// implements some common traits, like [Clone], and [PartialEq]; but also [One] (the identity
/// element used) as well as [AddAssign] and [SubAssign] (to work increment/decrement the index).
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

/// Iterator over a range
pub struct RangeIter<Idx, Direction> {
    current: Idx,
    limit: Idx,
    #[allow(unused)] direction: Direction,
    init: bool,
}

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
