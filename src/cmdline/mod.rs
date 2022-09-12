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
const CMDLINE_MAXSIZE: usize = 4096;
const INIT_ARGS_SEPARATOR: &str = " -- ";

/// The error type for command line building operations.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Null terminator identified inside command line.
    NullTerminator,
    /// No boot args inserted into cmdline.
    NoBootArgsInserted,
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
            Error::NullTerminator => {
                write!(f, "Null terminator identified inside command line.")
            }
            Error::NoBootArgsInserted => write!(f, "Cmdline cannot contain only init args."),
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

/// Trait that defines operations available for the arguments of a Cmdline.
pub trait UpdateArgs {
    /// Checks if there is still enough space for an insertion of `more` chars.
    ///
    /// This function does NOT guarantee that the maximum capacity given to the
    /// Cmdline object's instantiation was not reached when calling `as_cstring()`.
    /// It is just a way to protect the structs implementing this trait from
    /// abusive insertions.
    ///
    /// # Arguments
    ///
    /// * `more` - size of the new argument.
    fn has_capacity(&self, more: usize) -> bool;

    /// Validates and inserts a key=value pair into the args string.
    ///
    /// # Arguments
    ///
    /// * `key` - Key to be inserted in the args string.
    /// * `val` - Value corresponding to `key`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new();
    /// cl.boot_args_mut().insert_key_value("foo", "bar").unwrap();
    /// assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foo=bar\0");
    /// ```
    fn insert_key_value<T: AsRef<str>>(&mut self, key: T, val: T) -> Result<()> {
        let k = key.as_ref();
        let v = val.as_ref();

        valid_element(k)?;
        valid_element(v)?;

        let kv_str = format!("{}={}", k, v);

        self.insert_string(kv_str)
    }

    /// Validates and inserts a key=value1,...,valueN pair into the args string.
    ///
    /// # Arguments
    ///
    /// * `key` - Key to be inserted in the args string.
    /// * `vals` - Values corresponding to `key`.
    fn insert_multiple<T: AsRef<str>>(&mut self, key: T, vals: &[T]) -> Result<()> {
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

        self.insert_string(kv_str)
    }

    /// Validates and appends a string to the current args string.
    ///
    /// # Arguments
    ///
    /// * `slug` - String to be appended to the args string.
    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()>;
}

impl UpdateArgs for String {
    fn has_capacity(&self, more: usize) -> bool {
        // If the string is empty, no other space should be added before
        // appending the current argument; otherwise one whitespace is
        // needed before appending the new argument
        let auxiliary_space = if self.is_empty() { 0 } else { 1 };

        self.len() + auxiliary_space + more < CMDLINE_MAXSIZE
    }

    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        let s = slug.as_ref().trim();
        valid_str(s)?;

        if !self.has_capacity(s.len()) {
            return Err(Error::TooLarge);
        }

        if !self.is_empty() {
            self.push(' ');
        }

        self.push_str(s);

        Ok(())
    }
}

/// An abstraction for the boot arguments of a kernel command line.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct BootArgs(String);

impl Display for BootArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl BootArgs {
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
    /// let mut cl = Cmdline::new();
    /// cl.boot_args_mut()
    ///     .add_virtio_mmio_device(1 << 12, GuestAddress(0x1000), 5, Some(42))
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

        self.insert_string(&device_str)
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
}

impl UpdateArgs for BootArgs {
    fn has_capacity(&self, more: usize) -> bool {
        self.0.has_capacity(more)
    }

    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        self.0.insert_string(slug)
    }
}

/// An abstraction for the init arguments of a kernel command line.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InitArgs(String);

impl Display for InitArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl UpdateArgs for InitArgs {
    fn has_capacity(&self, more: usize) -> bool {
        self.0.has_capacity(more)
    }

    fn insert_string<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        self.0.insert_string(slug)
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
/// let mut cl = Cmdline::new();
/// cl.boot_args_mut().insert_string("foobar").unwrap();
/// assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foobar\0");
/// ```
#[derive(Clone, Eq, Ord, PartialOrd, Debug, Default)]
pub struct Cmdline {
    boot_args: BootArgs,
    init_args: InitArgs,
}

impl Cmdline {
    /// Constructs an empty [`Cmdline`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let cl = Cmdline::new();
    /// ```
    /// [`Cmdline`]: struct.Cmdline.html
    pub fn new() -> Cmdline {
        Cmdline {
            boot_args: BootArgs(String::new()),
            init_args: InitArgs(String::new()),
        }
    }

    /// Returns the representation of the boot arguments of the command
    /// line as a `BootArgs`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new();
    /// assert!(cl.boot_args_mut().insert_key_value("foo", "bar").is_ok());
    /// ```
    pub fn boot_args_mut(&mut self) -> &mut BootArgs {
        &mut self.boot_args
    }

    /// Returns the representation of the init arguments of the command
    /// line as an `InitArgs`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new();
    /// assert!(cl.init_args_mut().insert_key_value("foo", "bar").is_ok());
    /// ```
    pub fn init_args_mut(&mut self) -> &mut InitArgs {
        &mut self.init_args
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
    /// let mut cl = Cmdline::new();
    /// cl.boot_args_mut().insert_string("foo").unwrap();
    /// cl.init_args_mut().insert_string("bar").unwrap();
    /// assert_eq!(
    ///     cl.as_cstring().unwrap().as_bytes_with_nul(),
    ///     b"foo -- bar\0"
    /// );
    /// ```
    pub fn as_cstring(&self) -> Result<CString> {
        if self.boot_args.0.is_empty() {
            return if self.init_args.0.is_empty() {
                CString::new("".to_string()).map_err(|_| Error::NullTerminator)
            } else {
                Err(Error::NoBootArgsInserted)
            };
        }

        if self.init_args.0.is_empty() {
            if self.boot_args.0.len() < CMDLINE_MAXSIZE {
                CString::new(self.boot_args.0.to_string()).map_err(|_| Error::NullTerminator)
            } else {
                Err(Error::TooLarge)
            }
        } else if self.boot_args.0.len() + self.init_args.0.len() + INIT_ARGS_SEPARATOR.len()
            < CMDLINE_MAXSIZE
        {
            CString::new(format!(
                "{}{}{}",
                self.boot_args.0, INIT_ARGS_SEPARATOR, self.init_args.0
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

        if cmdline_size <= CMDLINE_MAXSIZE {
            Ok(Cmdline {
                boot_args: BootArgs(boot_args.trim().to_string()),
                init_args: InitArgs(init_args.trim().to_string()),
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
        let mut cl = Cmdline::new();
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
        assert!(cl
            .boot_args_mut()
            .insert_key_value("hello", "world")
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"hello=world\0"
        );
    }

    #[test]
    fn test_insert_multi() {
        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_key_value("hello", "world")
            .is_ok());
        assert!(cl.boot_args_mut().insert_key_value("foo", "bar").is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"hello=world foo=bar\0"
        );
    }

    #[test]
    fn test_insert_space() {
        let mut cl = Cmdline::new();
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a ", "b"),
            Err(Error::HasSpace)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a", "b "),
            Err(Error::HasSpace)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a ", "b "),
            Err(Error::HasSpace)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value(" a", "b"),
            Err(Error::HasSpace)
        );
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
    }

    #[test]
    fn test_insert_equals() {
        let mut cl = Cmdline::new();
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a=", "b"),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a", "b="),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a=", "b "),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("=a", "b"),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("a", "=b"),
            Err(Error::HasEquals)
        );
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
    }

    #[test]
    fn test_insert_emoji() {
        let mut cl = Cmdline::new();
        assert_eq!(
            cl.boot_args_mut().insert_key_value("heart", "💖"),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.boot_args_mut().insert_key_value("💖", "love"),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.boot_args_mut().insert_string("heart=💖"),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.boot_args_mut().insert_multiple("💖", &["heart", "love"]),
            Err(Error::InvalidAscii)
        );
        assert_eq!(
            cl.boot_args_mut().insert_multiple("heart", &["💖", "love"]),
            Err(Error::InvalidAscii)
        );
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
    }

    #[test]
    fn test_insert_string() {
        let mut cl = Cmdline::new();
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"\0");
        assert!(cl.boot_args_mut().insert_string("noapic").is_ok());
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"noapic\0");
        assert!(cl.boot_args_mut().insert_string("nopci").is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"noapic nopci\0"
        );
    }

    #[test]
    fn test_has_capacity() {
        let mut cl = Cmdline::new();
        assert!(cl.boot_args_mut().has_capacity(CMDLINE_MAXSIZE - 1));
        assert!(cl.init_args_mut().has_capacity(CMDLINE_MAXSIZE - 1));
        cl.boot_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 1])
                    .unwrap()
                    .as_str(),
            )
            .unwrap();
        assert!(!cl.boot_args_mut().has_capacity(1));
        assert!(cl.init_args_mut().has_capacity(CMDLINE_MAXSIZE - 1));

        cl.init_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 1])
                    .unwrap()
                    .as_str(),
            )
            .unwrap();
        assert!(!cl.init_args_mut().has_capacity(1));
        assert!(!cl.boot_args_mut().has_capacity(1));
    }

    #[test]
    fn test_insert_too_large() {
        // Testing on boot args side
        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 7])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert_eq!(
            cl.boot_args_mut().insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 6])
                    .unwrap()
                    .as_str()
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 1])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert_eq!(
            cl.boot_args_mut().insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE])
                    .unwrap()
                    .as_str()
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 9])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"]
            )
            .is_ok());
        assert_eq!(
            cl.boot_args_mut().insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 8])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"]
            ),
            Err(Error::TooLarge)
        );

        // Testing on init args side
        let mut cl = Cmdline::new();
        assert!(cl
            .init_args_mut()
            .insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 7])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert_eq!(
            cl.init_args_mut().insert_key_value(
                "hello",
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 6])
                    .unwrap()
                    .as_str()
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new();
        assert!(cl
            .init_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 1])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert_eq!(
            cl.init_args_mut().insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE])
                    .unwrap()
                    .as_str()
            ),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new();
        assert!(cl
            .init_args_mut()
            .insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 9])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"]
            )
            .is_ok());
        assert_eq!(
            cl.init_args_mut().insert_multiple(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 8])
                    .unwrap()
                    .as_str(),
                &["bar", "baz"]
            ),
            Err(Error::TooLarge)
        );

        // Testing combination between boot args and init args
        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE / 2])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert!(cl
            .init_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; (CMDLINE_MAXSIZE / 2) - 5])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert!(cl.as_cstring().is_ok());

        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 1])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert!(cl
            .init_args_mut()
            .insert_string(
                String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE - 1])
                    .unwrap()
                    .as_str()
            )
            .is_ok());
        assert_eq!(cl.as_cstring(), Err(Error::TooLarge));
    }

    #[test]
    fn test_add_virtio_mmio_device() {
        let mut cl = Cmdline::new();
        assert_eq!(
            cl.boot_args
                .add_virtio_mmio_device(0, GuestAddress(0), 0, None),
            Err(Error::MmioSize)
        );

        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        let mut expected_str = "virtio_mmio.device=1@0x0:1".to_string();
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );

        assert!(cl
            .boot_args
            .add_virtio_mmio_device(2 << 10, GuestAddress(0x100), 2, None)
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=2K@0x100:2");
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );

        assert!(cl
            .boot_args
            .add_virtio_mmio_device(3 << 20, GuestAddress(0x1000), 3, None)
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=3M@0x1000:3");
        assert_eq!(
            cl.as_cstring().unwrap(),
            CString::new(expected_str.as_bytes()).unwrap()
        );

        assert!(cl
            .boot_args
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
        let mut cl = Cmdline::new();

        let no_vals: Vec<&str> = vec![];
        assert_eq!(
            cl.boot_args_mut().insert_multiple("foo=", &no_vals),
            Err(Error::HasEquals)
        );
        assert_eq!(
            cl.boot_args_mut().insert_multiple("foo", &no_vals),
            Err(Error::MissingVal("foo".to_string()))
        );
        assert_eq!(
            cl.boot_args_mut().insert_multiple("foo", &["bar "]),
            Err(Error::HasSpace)
        );

        let mut cl = Cmdline::new();
        assert!(cl.boot_args_mut().insert_multiple("foo", &["bar"]).is_ok());
        assert_eq!(cl.as_cstring().unwrap().as_bytes_with_nul(), b"foo=bar\0");

        let mut cl = Cmdline::new();
        assert!(cl
            .boot_args_mut()
            .insert_multiple("foo", &["bar", "baz"])
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().as_bytes_with_nul(),
            b"foo=bar,baz\0"
        );
    }

    #[test]
    fn test_from_cmdline_for_vec() {
        let cl = Cmdline::new();
        assert_eq!(Vec::from(cl), vec![b'\0']);

        let cl = Cmdline::try_from("foo".to_string()).unwrap();
        assert_eq!(Vec::from(cl), vec![b'f', b'o', b'o', b'\0']);

        let mut cl = Cmdline::new();
        cl.init_args_mut().insert_string("foo--bar").unwrap();
        assert_eq!(Vec::from(cl), vec![b'\0']);
    }

    #[test]
    fn test_partial_eq() {
        let mut c1 = Cmdline::new();
        let mut c2 = Cmdline::new();

        c1.boot_args_mut().insert_string("hello world!").unwrap();
        c2.boot_args_mut().insert_string("hello").unwrap();
        assert_ne!(c1, c2);

        // `insert_string` also adds a whitespace before the string being inserted.
        c2.boot_args_mut().insert_string("world!").unwrap();
        assert_eq!(c1, c2);

        let mut cl1 = Cmdline::new();
        let mut cl2 = Cmdline::new();

        assert_eq!(cl1, cl2);
        assert!(cl1
            .boot_args
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        assert_ne!(cl1, cl2);
        assert!(cl2
            .boot_args
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        assert_eq!(cl1, cl2);
    }

    #[test]
    fn test_try_from() {
        let cl = Cmdline::try_from("hello=world foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "hello=world foo=bar");
        assert_eq!(cl.init_args.0, "");

        let cl = Cmdline::try_from("hello=world -- foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "hello=world");
        assert_eq!(cl.init_args.0, "foo=bar");

        let cl = Cmdline::try_from("hello=world foo=bar --  ".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "hello=world foo=bar");
        assert_eq!(cl.init_args.0, "");

        let cl = Cmdline::try_from("hello=world foo=bar  --".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "hello=world foo=bar");
        assert_eq!(cl.init_args.0, "");

        let cl = Cmdline::try_from("  -- hello=world foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "");
        assert_eq!(cl.init_args.0, "hello=world foo=bar");

        let cl = Cmdline::try_from("-- hello=world foo=bar".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "");
        assert_eq!(cl.init_args.0, "hello=world foo=bar");

        let cl = Cmdline::try_from("hello=world --foo=bar -- arg1 --arg2".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "hello=world --foo=bar");
        assert_eq!(cl.init_args.0, "arg1 --arg2");

        let cl = Cmdline::try_from("-- arg1 --arg2".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "");
        assert_eq!(cl.init_args.0, "arg1 --arg2");

        let cl = Cmdline::try_from("arg1-- arg2 --arg3".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "arg1-- arg2 --arg3");
        assert_eq!(cl.init_args.0, "");

        let cl = Cmdline::try_from("--arg1-- -- arg2 -- --arg3".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "--arg1--");
        assert_eq!(cl.init_args.0, "arg2 -- --arg3");

        let cl = Cmdline::try_from("a=\"b -- c\" d -- e ".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "a=\"b -- c\" d");
        assert_eq!(cl.init_args.0, "e");

        let cl = Cmdline::try_from("foo--bar=baz a=\"b -- c\"".to_string()).unwrap();

        assert_eq!(cl.boot_args.0, "foo--bar=baz a=\"b -- c\"");
        assert_eq!(cl.init_args.0, "");
    }

    #[test]
    fn test_error_try_from() {
        Cmdline::try_from(String::from_utf8(vec![b'X'; CMDLINE_MAXSIZE]).unwrap())
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
        let mut cl = Cmdline::new();

        assert_eq!(cl.as_cstring().unwrap().into_bytes_with_nul(), b"\0");
        assert!(cl.init_args_mut().insert_string("/etc/password").is_ok());
        assert_eq!(cl.as_cstring(), Err(Error::NoBootArgsInserted));
        assert_eq!(cl.boot_args.0, "");
        assert_eq!(cl.init_args.0, "/etc/password");
        assert!(cl
            .boot_args_mut()
            .insert_key_value("console", "ttyS0")
            .is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().into_bytes_with_nul(),
            b"console=ttyS0 -- /etc/password\0"
        );
        assert!(cl.boot_args_mut().insert_string("nomodules").is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().into_bytes_with_nul(),
            b"console=ttyS0 nomodules -- /etc/password\0"
        );
        assert!(cl.init_args_mut().insert_string("--param").is_ok());
        assert_eq!(
            cl.as_cstring().unwrap().into_bytes_with_nul(),
            b"console=ttyS0 nomodules -- /etc/password --param\0"
        );
    }
}
