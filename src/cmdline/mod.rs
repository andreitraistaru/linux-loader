// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
//
//! Helper for creating valid kernel command line strings.

use std::convert::TryFrom;
use std::ffi::CString;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::result;

use vm_memory::{Address, GuestAddress, GuestUsize};

/// The maximum length of a command line a Linux kernel might expect
/// to find in the guest's memory according to the specification:
/// https://www.kernel.org/doc/html/v4.14/admin-guide/kernel-parameters.html
const CMDLINE_MAX_SIZE: usize = 4096;
const INIT_ARGS_SEPARATOR: &str = " -- ";

/// The error type for command line building operations.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Null terminator identified inside command line.
    NullTerminator,
    /// No boot args inserted into cmdline.
    NoBootArgsInserted,
    /// Invalid capacity provided.
    InvalidCapacity,
    /// Operation would have resulted in a non-printable ASCII character.
    InvalidAscii,
    /// Key/Value Operation would have had a space in it.
    HasSpace,
    /// Key/Value Operation would have had an equals sign in it.
    HasEquals,
    /// Key/Value Operation was not passed a value.
    MissingVal(String),
    /// 0-sized virtio MMIO device passed to the kernel command line builder.
    MmioSize,
    /// Operation would have made the command line too large.
    TooLarge,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Error::NullTerminator => write!(f, "Null terminator identified inside command line."),
            Error::NoBootArgsInserted => write!(f, "Cmdline cannot contain only init args."),
            Error::InvalidCapacity => write!(f, "Invalid Cmdline capacity provided."),
            Error::InvalidAscii => write!(f, "String contains a non-printable ASCII character."),
            Error::HasSpace => write!(f, "String contains a space."),
            Error::HasEquals => write!(f, "String contains an equals sign."),
            Error::MissingVal(ref k) => write!(f, "Missing value for key {}.", k),
            Error::MmioSize => write!(
                f,
                "0-sized virtio MMIO device passed to the kernel command line builder."
            ),
            Error::TooLarge => write!(f, "Inserting string would make command line too long."),
        }
    }
}

impl std::error::Error for Error {}

/// Specialized [`Result`] type for command line operations.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
pub type Result<T> = result::Result<T, Error>;

fn valid_char(c: char) -> bool {
    matches!(c, ' '..='~')
}

fn valid_str(s: &str) -> Result<()> {
    if s.chars().all(valid_char) {
        Ok(())
    } else {
        Err(Error::InvalidAscii)
    }
}

fn valid_element(s: &str) -> Result<()> {
    if !s.chars().all(valid_char) {
        Err(Error::InvalidAscii)
    } else if s.contains(' ') {
        Err(Error::HasSpace)
    } else if s.contains('=') {
        Err(Error::HasEquals)
    } else {
        Ok(())
    }
}

/// Enum that defines type of arguments accepted by a Cmdline.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum CmdlineArgType {
    /// Boot argument from cmdline.
    BootArg,
    /// Init argument from cmdline.
    InitArg,
}

impl Display for CmdlineArgType {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            CmdlineArgType::BootArg => write!(f, "Boot argument type"),
            CmdlineArgType::InitArg => write!(f, "Init argument type"),
        }
    }
}

/// Trait that defines operations available for the arguments of a Cmdline.
pub trait UpdateArgs {
    /// Returns the size in bytes of the arguments representation.
    fn len(&self) -> usize;

    /// Checks is the arguments representation is empty.
    fn is_empty(&self) -> bool;

    /// Validates and appends a string to the current args string.
    ///
    /// # Arguments
    ///
    /// * `slug` - String to be appended to the args string.
    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()>;

    /// Returns the String representation of the arguments struct.
    fn as_string(&self) -> String;
}

impl UpdateArgs for String {
    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        let s = slug.as_ref().trim();
        valid_str(s)?;

        if !self.is_empty() {
            self.push(' ');
        }

        self.push_str(s);

        Ok(())
    }

    fn as_string(&self) -> String {
        self.to_string()
    }
}

/// An abstraction for the boot arguments of a kernel command line.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct BootArgs(String);

impl Display for BootArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_string())
    }
}

impl UpdateArgs for BootArgs {
    fn len(&self) -> usize {
        <String as UpdateArgs>::len(&self.0)
    }

    fn is_empty(&self) -> bool {
        <String as UpdateArgs>::is_empty(&self.0)
    }

    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        self.0.insert_string(slug)
    }

    fn as_string(&self) -> String {
        <String as UpdateArgs>::as_string(&self.0)
    }
}

/// An abstraction for the init arguments of a kernel command line.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InitArgs(String);

impl Display for InitArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_string())
    }
}

impl UpdateArgs for InitArgs {
    fn len(&self) -> usize {
        <String as UpdateArgs>::len(&self.0)
    }

    fn is_empty(&self) -> bool {
        <String as UpdateArgs>::is_empty(&self.0)
    }

    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        self.0.insert_string(slug)
    }

    fn as_string(&self) -> String {
        <String as UpdateArgs>::as_string(&self.0)
    }
}

/// A builder for a kernel command line string that validates the string
/// as it's being built.
///
/// # Examples
///
/// ```rust
/// # use linux_loader::cmdline::*;
/// # use std::ffi::CString;
/// let mut cl = Cmdline::new(10).unwrap();
/// cl.insert_string("foobar", CmdlineArgType::BootArg).unwrap();
/// assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foobar\0");
/// ```
#[derive(Clone, Eq, Ord, PartialOrd, Debug, Default)]
pub struct Cmdline {
    boot_args: BootArgs,
    init_args: InitArgs,
    capacity: usize,
}

impl Cmdline {
    /// Constructs an empty [`Cmdline`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let cl = Cmdline::new(10).unwrap();
    /// ```
    /// [`Cmdline`]: struct.Cmdline.html
    pub fn new(capacity: usize) -> Result<Cmdline> {
        if capacity == 0 {
            return Err(Error::InvalidCapacity);
        }

        Ok(Cmdline {
            boot_args: BootArgs(String::new()),
            init_args: InitArgs(String::new()),
            capacity,
        })
    }

    /// Tries to set a new capacity of the `Cmdline`. It fails when `new_capacity`
    /// is smaller than the C complatible representation of the current `Cmdline`
    /// (which requires to be null terminated)
    ///
    /// # Arguments
    ///
    /// * `new_capacity` - New capacity to be set..
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new(3).unwrap();
    /// assert!(cl.insert_string("foo", CmdlineArgType::BootArg).is_err());
    /// cl.set_capacity(4).unwrap();
    /// assert!(cl.insert_string("foo", CmdlineArgType::BootArg).is_ok());
    /// assert_eq!(cl.set_capacity(3), Err(Error::InvalidCapacity));
    /// ```
    pub fn set_capacity(&mut self, new_capacity: usize) -> Result<()> {
        if self.get_null_terminated_representation_size() <= new_capacity {
            self.capacity = new_capacity;

            Ok(())
        } else {
            Err(Error::InvalidCapacity)
        }
    }

    fn get_null_terminated_representation_size(&self) -> usize {
        // Computing current size of the cmdline
        let mut cmdline_size = self.boot_args.len() + 1; // for null terminator

        if !self.init_args.is_empty() {
            cmdline_size += INIT_ARGS_SEPARATOR.len() + self.init_args.len();
        }

        cmdline_size
    }

    fn has_capacity(&self, more: usize, args_type: CmdlineArgType) -> bool {
        let mut cmdline_size = self.get_null_terminated_representation_size();

        // Adding extra size required for the insertion of `more` bytes as a `args_type` argument

        // Checking if one extra space needs to be added before insertion of a new argument
        cmdline_size += match args_type {
            CmdlineArgType::BootArg => {
                if !self.boot_args.is_empty() {
                    1
                } else {
                    0
                }
            }
            CmdlineArgType::InitArg => {
                if !self.init_args.is_empty() {
                    1
                } else {
                    INIT_ARGS_SEPARATOR.len()
                }
            }
        };

        cmdline_size += more;

        cmdline_size <= self.capacity
    }

    /// Validates and inserts a key=value pair as a new cmdline argument.
    ///
    /// # Arguments
    ///
    /// * `key` - Key to be inserted in the args string.
    /// * `val` - Value corresponding to `key`.
    /// * `args_type` - Type of the new argument to be inserted.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new(10).unwrap();
    /// cl.insert_key_value("foo", "bar", CmdlineArgType::BootArg)
    ///     .unwrap();
    /// assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foo=bar\0");
    /// ```
    pub fn insert_key_value<T: AsRef<str>>(
        &mut self,
        key: T,
        val: T,
        args_type: CmdlineArgType,
    ) -> Result<()> {
        let k = key.as_ref();
        let v = val.as_ref();

        valid_element(k)?;
        valid_element(v)?;

        let kv_str = format!("{}={}", k, v);

        self.insert_string(kv_str, args_type)
    }

    /// Validates and inserts a key=value1,...,valueN pair as a new cmdline argument.
    ///
    /// # Arguments
    ///
    /// * `key` - Key to be inserted in the args string.
    /// * `vals` - Values corresponding to `key`.
    /// * `args_type` - Type of the new argument to be inserted.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new(20).unwrap();
    /// cl.insert_multiple("foo", &["bar", "baz"], CmdlineArgType::BootArg)
    ///     .unwrap();
    /// assert_eq!(
    ///     cl.as_cstring().unwrap().as_bytes_with_nul(),
    ///     b"foo=bar,baz\0"
    /// );
    /// ```
    pub fn insert_multiple<T: AsRef<str>>(
        &mut self,
        key: T,
        vals: &[T],
        args_type: CmdlineArgType,
    ) -> Result<()> {
        let k = key.as_ref();

        valid_element(k)?;
        if vals.is_empty() {
            return Err(Error::MissingVal(k.to_string()));
        }

        let kv_str = format!(
            "{}={}",
            k,
            vals.iter()
                .map(|v| -> Result<&str> {
                    valid_element(v.as_ref())?;
                    Ok(v.as_ref())
                })
                .collect::<Result<Vec<&str>>>()?
                .join(",")
        );

        self.insert_string(kv_str, args_type)
    }

    /// Validates and inserts a string as a new cmdline argument.
    ///
    /// # Arguments
    ///
    /// * `slug` - String to be appended to the args string.
    /// * `args_type` - Type of the new argument to be inserted.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new(10).unwrap();
    /// cl.insert_string("foo=bar", CmdlineArgType::BootArg)
    ///     .unwrap();
    /// assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foo=bar\0");
    /// ```
    pub fn insert_string<T: AsRef<str>>(
        &mut self,
        slug: T,
        args_type: CmdlineArgType,
    ) -> Result<()> {
        let s = slug.as_ref().trim();
        valid_str(s)?;

        if !self.has_capacity(s.len(), args_type) {
            return Err(Error::TooLarge);
        }

        match args_type {
            CmdlineArgType::BootArg => self.boot_args.insert_string(s),
            CmdlineArgType::InitArg => self.init_args.insert_string(s),
        }
    }

    /// Adds a virtio MMIO device to the kernel command line.
    ///
    /// Multiple devices can be specified, with multiple `virtio_mmio.device=` options. This
    /// function must be called once per device.
    /// The function appends a string of the following format to the kernel command line:
    /// `<size>@<baseaddr>:<irq>[:<id>]`.
    /// For more details see the [documentation] (section `virtio_mmio.device=`).
    ///
    /// # Arguments
    ///
    /// * `size` - size of the slot the device occupies on the MMIO bus.
    /// * `baseaddr` - physical base address of the device.
    /// * `irq` - interrupt number to be used by the device.
    /// * `id` - optional platform device ID.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// # use std::ffi::CString;
    /// # use vm_memory::{GuestAddress, GuestUsize};
    /// let mut cl = Cmdline::new(100).unwrap();
    /// cl.add_virtio_mmio_device(1 << 12, GuestAddress(0x1000), 5, Some(42))
    ///     .unwrap();
    /// assert_eq!(
    ///     cl.as_cstring().unwrap().as_bytes_with_nul(),
    ///     b"virtio_mmio.device=4K@0x1000:5:42\0"
    /// );
    /// ```
    ///
    /// [documentation]: https://www.kernel.org/doc/html/latest/admin-guide/kernel-parameters.html
    pub fn add_virtio_mmio_device(
        &mut self,
        size: GuestUsize,
        base_addr: GuestAddress,
        irq: u32,
        id: Option<u32>,
    ) -> Result<()> {
        if size == 0 {
            return Err(Error::MmioSize);
        }

        let mut device_str = format!(
            "virtio_mmio.device={}@0x{:x?}:{}",
            Self::guestusize_to_str(size),
            base_addr.raw_value(),
            irq
        );

        if let Some(id) = id {
            device_str.push_str(format!(":{}", id).as_str());
        }

        self.insert_string(&device_str, CmdlineArgType::BootArg)
    }

    // Converts a `GuestUsize` to a concise string representation, with multiplier suffixes.
    fn guestusize_to_str(size: GuestUsize) -> String {
        const KB_MULT: u64 = 1 << 10;
        const MB_MULT: u64 = KB_MULT << 10;
        const GB_MULT: u64 = MB_MULT << 10;

        if size % GB_MULT == 0 {
            return format!("{}G", size / GB_MULT);
        }
        if size % MB_MULT == 0 {
            return format!("{}M", size / MB_MULT);
        }
        if size % KB_MULT == 0 {
            return format!("{}K", size / KB_MULT);
        }
        size.to_string()
    }

    /// Returns a C compatible representation of the command line
    /// The Linux kernel expects a null terminated cmdline according to the source:
    /// https://elixir.bootlin.com/linux/v5.10.139/source/kernel/params.c#L179
    ///
    /// To get bytes of the cmdline to be written in guest's memory (including the
    /// null terminator) from this representation, use CString::as_bytes_with_nul()
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new(20).unwrap();
    /// cl.insert_string("foo", CmdlineArgType::BootArg).unwrap();
    /// cl.insert_string("bar", CmdlineArgType::InitArg).unwrap();
    /// assert_eq!(
    ///     cl.as_cstring().unwrap().as_bytes_with_nul(),
    ///     b"foo -- bar\0"
    /// );
    /// ```
    pub fn as_cstring(&self) -> Result<CString> {
        if self.boot_args.is_empty() {
            return if self.init_args.is_empty() {
                CString::new("".to_string()).map_err(|_| Error::NullTerminator)
            } else {
                Err(Error::NoBootArgsInserted)
            };
        }

        if self.init_args.is_empty() {
            if self.boot_args.len() < self.capacity {
                CString::new(self.boot_args.as_string()).map_err(|_| Error::NullTerminator)
            } else {
                Err(Error::TooLarge)
            }
        } else if self.boot_args.len() + self.init_args.len() + INIT_ARGS_SEPARATOR.len()
            < self.capacity
        {
            CString::new(format!(
                "{}{}{}",
                self.boot_args.as_string(),
                INIT_ARGS_SEPARATOR,
                self.init_args.as_string()
            ))
            .map_err(|_| Error::NullTerminator)
        } else {
            Err(Error::TooLarge)
        }
    }
}

fn check_outside_double_quotes(slug: &str) -> bool {
    slug.matches('\"').count() % 2 == 0
}

impl TryFrom<String> for Cmdline {
    type Error = String;

    fn try_from(cmdline_raw: String) -> result::Result<Self, Self::Error> {
        // Checking for INIT_ARGS_SEPARATOR to extract boot arguments and init arguments from the
        // cmdline string provided by user; the INIT_ARGS_SEPARATOR should NOT be inside a double
        // quotes pair in order to be interpreted as a delimiter by the Linux kernel:
        // https://www.kernel.org/doc/html/v4.14/admin-guide/kernel-parameters.html
        let (mut boot_args, mut init_args) = match cmdline_raw
            .match_indices(INIT_ARGS_SEPARATOR)
            .find(|&x| check_outside_double_quotes(&cmdline_raw[..(x.0)]))
        {
            None => {
                // We still need to check if the given cmdline doesn't contain only init args
                // such that the '-- ' should exist at the beginning of the string
                match cmdline_raw.split_once("-- ") {
                    None => {
                        // We still need to check if the given cmdline doesn't contain only boot
                        // args and the ' --' isn't added at the end of the string
                        match cmdline_raw.split_once(" --") {
                            None => (cmdline_raw.as_str(), ""),
                            Some((boot_args_section, _)) => (boot_args_section, ""),
                        }
                    }
                    Some((boot_args_section, init_args_section)) => {
                        // We have to check that '-- ' is at the beginning of cmdline, otherwise
                        // it is part of a boot argument and should NOT be handled as delimiter
                        if boot_args_section.is_empty() {
                            ("", init_args_section)
                        } else {
                            (cmdline_raw.as_str(), "")
                        }
                    }
                }
            }
            Some((delimiter_index, _)) => (
                &cmdline_raw[..delimiter_index],
                &cmdline_raw[(delimiter_index + INIT_ARGS_SEPARATOR.len())..],
            ),
        };

        boot_args = boot_args.trim();
        init_args = init_args.trim();

        let mut cmdline_size = boot_args.len() + 1; // for the null terminator

        if !init_args.is_empty() {
            cmdline_size += init_args.len() + INIT_ARGS_SEPARATOR.len();
        }

        if cmdline_size <= CMDLINE_MAX_SIZE {
            Ok(Cmdline {
                boot_args: BootArgs(boot_args.trim().to_string()),
                init_args: InitArgs(init_args.trim().to_string()),
                capacity: CMDLINE_MAX_SIZE,
            })
        } else {
            Err("Cmdline length exceeds the limit.".to_string())
        }
    }
}

impl From<Cmdline> for Vec<u8> {
    fn from(cmdline: Cmdline) -> Vec<u8> {
        match cmdline.as_cstring() {
            Ok(cmdline_cstring) => cmdline_cstring.into_bytes_with_nul(),
            Err(_) => Vec::from([0u8]),
        }
    }
}

impl PartialEq for Cmdline {
    fn eq(&self, other: &Self) -> bool {
        self.as_cstring() == other.as_cstring()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryFrom;
    use std::ffi::CString;

    #[test]
    fn test_insert_hello_world() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
        assert!(cl
            .insert_key_value("hello", "world", CmdlineArgType::BootArg)
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"hello=world\0"
        );
    }

    #[test]
    fn test_insert_multi() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_key_value("hello", "world", CmdlineArgType::BootArg)
            .is_ok());
        assert!(cl
            .insert_key_value("foo", "bar", CmdlineArgType::BootArg)
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"hello=world foo=bar\0"
        );
    }

    #[test]
    fn test_insert_space() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(
            cl.insert_key_value("a ", "b", CmdlineArgType::BootArg),
            Err(Error::HasSpace)
        );
        assert_eq!(
            cl.insert_key_value("a", "b ", CmdlineArgType::BootArg),
            Err(Error::HasSpace)
        );
        assert_eq!(
            cl.insert_key_value("a ", "b ", CmdlineArgType::BootArg),
            Err(Error::HasSpace)
        );
        assert_eq!(
            cl.insert_key_value(" a", "b", CmdlineArgType::BootArg),
            Err(Error::HasSpace)
        );
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
    }

    #[test]
    fn test_insert_equals() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(
            cl.insert_key_value("a=", "b", CmdlineArgType::BootArg),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.insert_key_value("a", "b=", CmdlineArgType::BootArg),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.insert_key_value("a=", "b ", CmdlineArgType::BootArg),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.insert_key_value("=a", "b", CmdlineArgType::BootArg),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.insert_key_value("a", "=b", CmdlineArgType::BootArg),
            Err(Error::HasEquals)
        );
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
    }

    #[test]
    fn test_insert_emoji() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(
            cl.insert_key_value("heart", "💖", CmdlineArgType::BootArg),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.insert_key_value("💖", "love", CmdlineArgType::BootArg),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.insert_string("heart=💖", CmdlineArgType::BootArg),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.insert_multiple("💖", &["heart", "love"], CmdlineArgType::BootArg),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.insert_multiple("heart", &["💖", "love"], CmdlineArgType::BootArg),
            Err(Error::InvalidAscii)
        );
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
    }

    #[test]
    fn test_insert_string() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
        assert!(cl.insert_string("noapic", CmdlineArgType::BootArg).is_ok());
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"noapic\0");
        assert!(cl.insert_string("nopci", CmdlineArgType::BootArg).is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"noapic nopci\0"
        );
    }

    #[test]
    fn test_insert_too_large() {
        // Testing on boot args side
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 7])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::BootArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 6])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::BootArg
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 1])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::BootArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::BootArg
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 9])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"],
                CmdlineArgType::BootArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 8])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"],
                CmdlineArgType::BootArg
            ),
            Err(Error::TooLarge)
        );

        // Testing on init args side
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 11])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::InitArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 10])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::InitArg
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 5])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::InitArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 4])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::InitArg
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 13])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"],
                CmdlineArgType::InitArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 12])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"],
                CmdlineArgType::InitArg
            ),
            Err(Error::TooLarge)
        );

        // Testing combination between boot args and init args
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE / 2])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::BootArg
            )
            .is_ok());
        assert!(cl
            .insert_string(
                String::from_utf8(vec![b'X'; (CMDLINE_MAX_SIZE / 2) - 5])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::InitArg
            )
            .is_ok());
        assert!(cl.as_cstring().is_ok());

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE - 6])
                    .unwrap()
                    .as_str(),
                CmdlineArgType::BootArg
            )
            .is_ok());
        assert_eq!(
            cl.insert_string("fo", CmdlineArgType::InitArg),
            Err(Error::TooLarge)
        );
        assert!(cl.insert_string("f", CmdlineArgType::InitArg).is_ok());
        assert!(cl.as_cstring().is_ok());
    }

    #[test]
    fn test_add_virtio_mmio_device() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(
            cl.add_virtio_mmio_device(0, GuestAddress(0), 0, None),
            Err(Error::MmioSize)
        );

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        let mut expected_str = "virtio_mmio.device=1@0x0:1".to_string();
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );

        assert!(cl
            .add_virtio_mmio_device(2 << 10, GuestAddress(0x100), 2, None)
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=2K@0x100:2");
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );

        assert!(cl
            .add_virtio_mmio_device(3 << 20, GuestAddress(0x1000), 3, None)
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=3M@0x1000:3");
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );

        assert!(cl
            .add_virtio_mmio_device(4 << 30, GuestAddress(0x0001_0000), 4, Some(42))
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=4G@0x10000:4:42");
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );
    }

    #[test]
    fn test_insert_kv() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();

        let no_vals: Vec<&str> = vec![];
        assert_eq!(
            cl.insert_multiple("foo=", &no_vals, CmdlineArgType::BootArg),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.insert_multiple("foo", &no_vals, CmdlineArgType::BootArg),
            Err(Error::MissingVal("foo".to_string()))
        );
        assert_eq!(
            cl.insert_multiple("foo", &["bar "], CmdlineArgType::BootArg),
            Err(Error::HasSpace)
        );

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_multiple("foo", &["bar"], CmdlineArgType::BootArg)
            .is_ok());
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foo=bar\0");

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert!(cl
            .insert_multiple("foo", &["bar", "baz"], CmdlineArgType::BootArg)
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"foo=bar,baz\0"
        );
    }

    #[test]
    fn test_from_cmdline_for_vec() {
        let cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        assert_eq!(Vec::from(cl), vec![b'\0']);

        let cl = Cmdline::try_from("foo".to_string()).unwrap();
        assert_eq!(Vec::from(cl), vec![b'f', b'o', b'o', b'\0']);

        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        cl.insert_string("foo--bar", CmdlineArgType::InitArg)
            .unwrap();
        assert_eq!(Vec::from(cl), vec![b'\0']);
    }

    #[test]
    fn test_partial_eq() {
        let mut c1 = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        let mut c2 = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();

        c1.insert_string("hello world!", CmdlineArgType::BootArg)
            .unwrap();
        c2.insert_string("hello", CmdlineArgType::BootArg).unwrap();
        assert_ne!(c1, c2);

        // `insert_string` also adds a whitespace before the string being inserted.
        c2.insert_string("world!", CmdlineArgType::BootArg).unwrap();
        assert_eq!(c1, c2);

        let mut cl1 = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();
        let mut cl2 = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();

        assert_eq!(cl1, cl2);
        assert!(cl1
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        assert_ne!(cl1, cl2);
        assert!(cl2
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        assert_eq!(cl1, cl2);
    }

    #[test]
    fn test_try_from() {
        let cl = Cmdline::try_from("hello=world foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "hello=world foo=bar");
        assert_eq!(cl.init_args.as_string(), "");

        let cl = Cmdline::try_from("hello=world -- foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "hello=world");
        assert_eq!(cl.init_args.as_string(), "foo=bar");

        let cl = Cmdline::try_from("hello=world foo=bar --  ".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "hello=world foo=bar");
        assert_eq!(cl.init_args.as_string(), "");

        let cl = Cmdline::try_from("hello=world foo=bar  --".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "hello=world foo=bar");
        assert_eq!(cl.init_args.as_string(), "");

        let cl = Cmdline::try_from("  -- hello=world foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "");
        assert_eq!(cl.init_args.as_string(), "hello=world foo=bar");

        let cl = Cmdline::try_from("-- hello=world foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "");
        assert_eq!(cl.init_args.as_string(), "hello=world foo=bar");

        let cl = Cmdline::try_from("hello=world --foo=bar -- arg1 --arg2".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "hello=world --foo=bar");
        assert_eq!(cl.init_args.as_string(), "arg1 --arg2");

        let cl = Cmdline::try_from("-- arg1 --arg2".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "");
        assert_eq!(cl.init_args.as_string(), "arg1 --arg2");

        let cl = Cmdline::try_from("arg1-- arg2 --arg3".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "arg1-- arg2 --arg3");
        assert_eq!(cl.init_args.as_string(), "");

        let cl = Cmdline::try_from("--arg1-- -- arg2 -- --arg3".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "--arg1--");
        assert_eq!(cl.init_args.as_string(), "arg2 -- --arg3");

        let cl = Cmdline::try_from("a=\"b -- c\" d -- e ".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "a=\"b -- c\" d");
        assert_eq!(cl.init_args.as_string(), "e");

        let cl = Cmdline::try_from("foo--bar=baz a=\"b -- c\"".to_string()).unwrap();

        assert_eq!(cl.boot_args.as_string(), "foo--bar=baz a=\"b -- c\"");
        assert_eq!(cl.init_args.as_string(), "");
    }

    #[test]
    fn test_error_try_from() {
        Cmdline::try_from(String::from_utf8(vec![b'X'; CMDLINE_MAX_SIZE]).unwrap())
            .map_err(|err| assert_eq!(err, "Cmdline length exceeds the limit."))
            .expect_err("Testing try_from.");

        let cl = Cmdline::try_from("console=ttyS0 nomodules -- /etc/password --param".to_string())
            .unwrap();
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"console=ttyS0 nomodules -- /etc/password --param\0"
        );
    }

    #[test]
    fn test_as_cstring() {
        let mut cl = Cmdline::new(CMDLINE_MAX_SIZE).unwrap();

        assert_eq!(cl.as_cstring().unwrap().into_bytes_with_nul(), b"\0");
        assert!(cl
            .insert_string("/etc/password", CmdlineArgType::InitArg)
            .is_ok());
        assert_eq!(cl.as_cstring(), Err(Error::NoBootArgsInserted));
        assert_eq!(cl.boot_args.as_string(), "");
        assert_eq!(cl.init_args.as_string(), "/etc/password");
        assert!(cl
            .insert_key_value("console", "ttyS0", CmdlineArgType::BootArg)
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().into_bytes_with_nul(),
            b"console=ttyS0 -- /etc/password\0"
        );
        assert!(cl
            .insert_string("nomodules", CmdlineArgType::BootArg)
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().into_bytes_with_nul(),
            b"console=ttyS0 nomodules -- /etc/password\0"
        );
        assert!(cl.insert_string("--param", CmdlineArgType::InitArg).is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().into_bytes_with_nul(),
            b"console=ttyS0 nomodules -- /etc/password --param\0"
        );
    }
}
