//! [![CI Status]][workflow] [![MSRV]][repo] [![Latest Version]][crates.io] [![Rust Doc Crate]][docs.rs] [![Rust Doc Main]][docs]
//!
//! [CI Status]: https://img.shields.io/github/actions/workflow/status/juntyr/pyo3-error/ci.yml?branch=main
//! [workflow]: https://github.com/juntyr/pyo3-error/actions/workflows/ci.yml?query=branch%3Amain
//!
//! [MSRV]: https://img.shields.io/badge/MSRV-1.63.0-blue
//! [repo]: https://github.com/juntyr/pyo3-error
//!
//! [Latest Version]: https://img.shields.io/crates/v/pyo3-error
//! [crates.io]: https://crates.io/crates/pyo3-error
//!
//! [Rust Doc Crate]: https://img.shields.io/docsrs/pyo3-error
//! [docs.rs]: https://docs.rs/pyo3-error/
//!
//! [Rust Doc Main]: https://img.shields.io/badge/docs-main-blue
//! [docs]: https://juntyr.github.io/pyo3-error/pyo3_error
//!
//! Unified error causality chains across Rust and Python using [`PyErrChain`].

use std::{borrow::Cow, error::Error, fmt, io};

use pyo3::{exceptions::PyException, intern, prelude::*, sync::GILOnceCell, types::IntoPyDict};

/// [`PyErrChain`] wraps a [`PyErr`] together with its causality chain.
///
/// Unlike [`PyErr`], [`PyErrChain`]'s implementation of [`std::error::Error`]
/// provides access to the error cause through the [`std::error::Error::source`]
/// method.
///
/// Note that since [`PyErr`]s can be readily cloned, the [`PyErrChain`] only
/// captures the causality chain at the time of construction. Calling
/// [`PyErr::set_cause`] on a clone of the wrapped error after construction will
/// thus not update the chain as captured by this [`PyErrChain`].
pub struct PyErrChain {
    err: PyErr,
    cause: Option<Box<Self>>,
}

impl PyErrChain {
    /// Create a new [`PyErrChain`] from `err`.
    ///
    /// The error's causality chain, as expressed by
    /// [`std::error::Error::source`], is translated into a [`PyErr::cause`]
    /// chain.
    ///
    /// If any error in the chain is a [`PyErrChain`] or a [`PyErr`], it is
    /// extracted directly. All other error types are translated into [`PyErr`]s
    /// using [`PyException::new_err`] with `format!("{}", err)`.
    ///
    /// If you want to customize the translation from [`std::error::Error`] into
    /// [`PyErr`], please use [`Self::new_with_translator`] instead.
    ///
    /// This constructor is equivalent to chaining [`Self::pyerr_from_err`] with
    /// [`Self::from_pyerr`].
    #[must_use]
    #[inline]
    pub fn new<T: Into<Box<dyn Error + 'static>>>(py: Python, err: T) -> Self {
        Self::from_pyerr(py, Self::pyerr_from_err(py, err))
    }

    /// Create a new [`PyErrChain`] from `err` using a custom translator from
    /// [`std::error::Error`] to [`PyErr`].
    ///
    /// The error's causality chain, as expressed by
    /// [`std::error::Error::source`], is translated into a [`PyErr::cause`]
    /// chain.
    ///
    /// If any error in the chain is a [`PyErrChain`] or a [`PyErr`], it is
    /// extracted directly. All other error types first attempt to be translated
    /// into [`PyErr`]s using the [`AnyErrorToPyErr`] and [`MapErrorToPyErr`].
    /// As a fallback, all remaining errors are translated into [`PyErr`]s using
    /// [`PyException::new_err`] with `format!("{}", err)`.
    ///
    /// This constructor is equivalent to chaining
    /// [`Self::pyerr_from_err_with_translator`] with [`Self::from_pyerr`].
    #[must_use]
    #[inline]
    pub fn new_with_translator<
        E: Into<Box<dyn Error + 'static>>,
        T: AnyErrorToPyErr,
        M: MapErrorToPyErr,
    >(
        py: Python,
        err: E,
    ) -> Self {
        Self::from_pyerr(py, Self::pyerr_from_err_with_translator::<E, T, M>(py, err))
    }

    /// Transform an `err` implementing [`std::error::Error`] into a [`PyErr`]
    /// that preserves the error's causality chain.
    ///
    /// The error's causality chain, as expressed by
    /// [`std::error::Error::source`], is translated into a [`PyErr::cause`]
    /// chain.
    ///
    /// If any error in the chain is a [`PyErrChain`] or a [`PyErr`], it is
    /// extracted directly. All other error types are translated into [`PyErr`]s
    /// using [`PyException::new_err`] with `format!("{}", err)`.
    ///
    /// If you want to customize the translation from [`std::error::Error`] into
    /// [`PyErr`], please use [`Self::pyerr_from_err_with_translator`] instead.
    #[must_use]
    #[inline]
    pub fn pyerr_from_err<T: Into<Box<dyn Error + 'static>>>(py: Python, err: T) -> PyErr {
        Self::pyerr_from_err_with_translator::<T, ErrorNoPyErr, DowncastToPyErr>(py, err)
    }

    /// Transform an `err` implementing [`std::error::Error`] into a [`PyErr`]
    /// that preserves the error's causality chain using a custom translator.
    ///
    /// The error's causality chain, as expressed by
    /// [`std::error::Error::source`], is translated into a [`PyErr::cause`]
    /// chain.
    ///
    /// If any error in the chain is a [`PyErrChain`] or a [`PyErr`], it is
    /// extracted directly. All other error types first attempt to be translated
    /// into [`PyErr`]s using the [`AnyErrorToPyErr`] and [`MapErrorToPyErr`].
    /// As a fallback, all remaining errors are translated into [`PyErr`]s using
    /// [`PyException::new_err`] with `format!("{}", err)`.
    #[must_use]
    pub fn pyerr_from_err_with_translator<
        E: Into<Box<dyn Error + 'static>>,
        T: AnyErrorToPyErr,
        M: MapErrorToPyErr,
    >(
        py: Python,
        err: E,
    ) -> PyErr {
        let err: Box<dyn Error + 'static> = err.into();

        let err = match M::try_map(py, err, |err: Box<Self>| err.into_pyerr()) {
            Ok(err) => return err,
            Err(err) => err,
        };
        let err = match M::try_map(py, err, |err: Box<PyErr>| *err) {
            Ok(err) => return err,
            Err(err) => err,
        };

        let mut chain = Vec::new();

        let mut source = err.source();
        let mut cause = None;

        while let Some(err) = source.take() {
            if let Some(err) = M::try_map_ref(py, err, |err: &Self| err.as_pyerr().clone_ref(py)) {
                cause = err.cause(py);
                chain.push(err);
                break;
            }
            if let Some(err) = M::try_map_ref(py, err, |err: &PyErr| err.clone_ref(py)) {
                cause = err.cause(py);
                chain.push(err);
                break;
            }

            source = err.source();

            #[allow(clippy::option_if_let_else)]
            chain.push(match T::try_from_err_ref::<M>(py, err) {
                Some(err) => err,
                None => PyException::new_err(format!("{err}")),
            });
        }

        while let Some(err) = chain.pop() {
            err.set_cause(py, cause.take());
            cause = Some(err);
        }

        let err = match T::try_from_err::<M>(py, err) {
            Ok(err) => err,
            Err(err) => PyException::new_err(format!("{err}")),
        };
        err.set_cause(py, cause);

        err
    }

    /// Wrap a [`PyErr`] and capture its causality chain, as expressed by
    /// [`PyErr::cause`].
    #[must_use]
    pub fn from_pyerr(py: Python, err: PyErr) -> Self {
        let mut chain = Vec::new();

        let mut cause = err.cause(py);

        while let Some(err) = cause.take() {
            cause = err.cause(py);
            chain.push(Self { err, cause: None });
        }

        let mut cause = None;

        while let Some(mut err) = chain.pop() {
            err.cause = cause.take();
            cause = Some(Box::new(err));
        }

        Self { err, cause }
    }

    /// Extract the wrapped [`PyErr`].
    #[must_use]
    pub fn into_pyerr(self) -> PyErr {
        self.err
    }

    /// Get a reference to the wrapped [`PyErr`].
    ///
    /// Note that while [`PyErr::set_cause`] can be called on the returned
    /// [`PyErr`], the change in causality chain will not be reflected in
    /// this [`PyErrChain`].
    #[must_use]
    pub const fn as_pyerr(&self) -> &PyErr {
        &self.err
    }

    /// Get a reference to the cause of the wrapped [`PyErr`].
    ///
    /// Note that while [`PyErr::set_cause`] can be called on the returned
    /// [`PyErr`], the change in causality chain will not be reflected in
    /// this [`PyErrChain`].
    #[must_use]
    pub fn cause(&self) -> Option<&PyErr> {
        self.cause.as_deref().map(Self::as_pyerr)
    }

    /// Clone the [`PyErrChain`].
    ///
    /// This requires the GIL, which is why [`PyErrChain`] does not implement
    /// [`Clone`].
    ///
    /// Note that all elements of the cloned [`PyErrChain`] will be shared using
    /// reference counting in Python with the existing [`PyErrChain`] `self`.
    #[must_use]
    pub fn clone_ref(&self, py: Python) -> Self {
        Self {
            err: self.err.clone_ref(py),
            cause: self
                .cause
                .as_ref()
                .map(|cause| Box::new(cause.clone_ref(py))),
        }
    }
}

impl fmt::Debug for PyErrChain {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        Python::with_gil(|py| {
            let traceback = self.err.traceback(py).map(|tb| {
                tb.format()
                    .map_or(Cow::Borrowed("<traceback str() failed>"), |tb| {
                        Cow::Owned(tb)
                    })
            });

            fmt.debug_struct("PyErrChain")
                .field("type", &self.err.get_type(py))
                .field("value", self.err.value(py))
                .field("traceback", &traceback)
                .field("cause", &self.cause)
                .finish()
        })
    }
}

impl fmt::Display for PyErrChain {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.err, fmt)
    }
}

impl Error for PyErrChain {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.cause.as_deref().map(|cause| cause as &dyn Error)
    }
}

impl From<PyErr> for PyErrChain {
    fn from(err: PyErr) -> Self {
        Python::with_gil(|py| Self::from_pyerr(py, err))
    }
}

impl From<PyErrChain> for PyErr {
    fn from(err: PyErrChain) -> Self {
        err.into_pyerr()
    }
}

/// Utility trait to try to translate from [`std::error::Error`] to [`PyErr`].
///
/// [`ErrorNoPyErr`] may be used to always fail at translating.
///
/// [`IoErrorToPyErr`] may be used to translate [`std::io::Error`] to [`PyErr`].
pub trait AnyErrorToPyErr {
    /// Try to translate from a boxed `err` to a [`PyErr`], or return the `err`.
    ///
    /// When a strongly typed translation from some specific error type `E` to a
    /// [`PyErr`] is attempted, [`MapErrorToPyErr::try_map`] should be used to allow
    /// the mapper to test for `E` in addition to wrapped errors such as
    /// `MyError<E>`.
    ///
    /// # Errors
    ///
    /// Returns the original `err` if translating to a [`PyErr`] failed.
    fn try_from_err<T: MapErrorToPyErr>(
        py: Python,
        err: Box<dyn Error + 'static>,
    ) -> Result<PyErr, Box<dyn Error + 'static>>;

    /// Try to translate from an `err` reference to a [`PyErr`], or return
    /// [`None`].
    ///
    /// When a strongly typed translation from some specific error type `E` to a
    /// [`PyErr`] is attempted, [`MapErrorToPyErr::try_map_ref`] should be used to
    /// allow the mapper to test for `E` in addition to wrapped errors such as
    /// `MyError<E>`.
    ///
    fn try_from_err_ref<T: MapErrorToPyErr>(
        py: Python,
        err: &(dyn Error + 'static),
    ) -> Option<PyErr>;
}

/// Utility trait to try to translate via specific error types `E` implementing
/// [`std::error::Error`] and wrapped errors such as `MyError<E>` to [`PyErr`]s.
///
/// [`DowncastToPyErr`] may be used to only try to translate via `E` using
/// downcasting.
pub trait MapErrorToPyErr {
    /// Try to map from a boxed `err` via the specific error type `T` or wrapped
    /// errors such as `MyError<E>` to a [`PyErr`], or return the `err`.
    ///
    /// The `map` function should be used to access the provided mapping from
    /// `T` to [`PyErr`].
    ///
    /// # Errors
    ///
    /// Returns the original `err` if mapping to a [`PyErr`] failed.
    fn try_map<T: Error + 'static>(
        py: Python,
        err: Box<dyn Error + 'static>,
        map: impl FnOnce(Box<T>) -> PyErr,
    ) -> Result<PyErr, Box<dyn Error + 'static>>;

    /// Try to map from a boxed `err` via the specific error type `T` or wrapped
    /// errors such as `MyError<E>` to a [`PyErr`], or return the `err`.
    ///
    /// The `map` function should be used to access the provided mapping from
    /// `T` to [`PyErr`].
    ///
    /// # Errors
    ///
    /// Returns the original `err` if mapping to a [`PyErr`] failed.
    fn try_map_send_sync<T: Error + 'static>(
        py: Python,
        err: Box<dyn Error + Send + Sync + 'static>,
        map: impl FnOnce(Box<T>) -> PyErr,
    ) -> Result<PyErr, Box<dyn Error + Send + Sync + 'static>>;

    /// Try to map from an `err` reference via the specific error type `T` or
    /// wrapped errors such as `MyError<E>` to a [`PyErr`], or return [`None`].
    ///
    /// The `map` function should be used to access the provided mapping from
    /// `&T` to [`PyErr`].
    fn try_map_ref<T: Error + 'static>(
        py: Python,
        err: &(dyn Error + 'static),
        map: impl FnOnce(&T) -> PyErr,
    ) -> Option<PyErr>;
}

/// Never attempt to translate any [`std::error::Error`] to [`PyErr`] when used
/// as [`AnyErrorToPyErr`].
pub struct ErrorNoPyErr;

impl AnyErrorToPyErr for ErrorNoPyErr {
    #[inline]
    fn try_from_err<T: MapErrorToPyErr>(
        _py: Python,
        err: Box<dyn Error + 'static>,
    ) -> Result<PyErr, Box<dyn Error + 'static>> {
        Err(err)
    }

    #[inline]
    fn try_from_err_ref<T: MapErrorToPyErr>(
        _py: Python,
        _err: &(dyn Error + 'static),
    ) -> Option<PyErr> {
        None
    }
}

/// Translate [`std::io::Error`] to [`PyErr`] when used as [`AnyErrorToPyErr`].
pub struct IoErrorToPyErr;

impl AnyErrorToPyErr for IoErrorToPyErr {
    fn try_from_err<T: MapErrorToPyErr>(
        py: Python,
        err: Box<dyn Error + 'static>,
    ) -> Result<PyErr, Box<dyn Error + 'static>> {
        T::try_map(py, err, |err: Box<io::Error>| {
            let kind = err.kind();

            if err.get_ref().is_some() {
                #[allow(clippy::unwrap_used)] // we just checked that it will be `Some(_)`
                let err = err.into_inner().unwrap();

                let err = match T::try_map_send_sync(py, err, |err: Box<PyErr>| *err) {
                    Ok(err) => return err,
                    Err(err) => err,
                };

                let err =
                    match T::try_map_send_sync(py, err, |err: Box<PyErrChain>| err.into_pyerr()) {
                        Ok(err) => return err,
                        Err(err) => err,
                    };

                return PyErr::from(io::Error::new(kind, err));
            }

            PyErr::from(*err)
        })
    }

    fn try_from_err_ref<T: MapErrorToPyErr>(
        py: Python,
        err: &(dyn Error + 'static),
    ) -> Option<PyErr> {
        T::try_map_ref(py, err, |err: &io::Error| {
            if let Some(err) = err.get_ref() {
                if let Some(err) = T::try_map_ref(py, err, |err: &PyErr| err.clone_ref(py)) {
                    return err;
                }

                if let Some(err) =
                    T::try_map_ref(py, err, |err: &PyErrChain| err.as_pyerr().clone_ref(py))
                {
                    return err;
                }
            }

            PyErr::from(io::Error::new(err.kind(), format!("{err}")))
        })
    }
}

/// Try to map a [`std::error::Error`] via a specific error type `T` to a
/// [`PyErr`] by downcasting when used as [`MapErrorToPyErr`];
pub struct DowncastToPyErr;

impl MapErrorToPyErr for DowncastToPyErr {
    fn try_map<T: Error + 'static>(
        _py: Python,
        err: Box<dyn Error + 'static>,
        map: impl FnOnce(Box<T>) -> PyErr,
    ) -> Result<PyErr, Box<dyn Error + 'static>> {
        err.downcast().map(map)
    }

    fn try_map_send_sync<T: Error + 'static>(
        _py: Python,
        err: Box<dyn Error + Send + Sync + 'static>,
        map: impl FnOnce(Box<T>) -> PyErr,
    ) -> Result<PyErr, Box<dyn Error + Send + Sync + 'static>> {
        err.downcast().map(map)
    }

    fn try_map_ref<T: Error + 'static>(
        _py: Python,
        err: &(dyn Error + 'static),
        map: impl FnOnce(&T) -> PyErr,
    ) -> Option<PyErr> {
        err.downcast_ref().map(map)
    }
}

#[allow(clippy::missing_panics_doc)]
/// Utility function to add a traceback with the error's `file`, `line`, and
/// `column` location information to the `err`.
///
/// This function may be used when implementing [`AnyErrorToPyErr`] or
/// [`MapErrorToPyErr`] to pythonize any available error location information.
#[must_use]
pub fn err_with_location(py: Python, err: PyErr, file: &str, line: u32, column: u32) -> PyErr {
    const RAISE: &str = "raise err";

    static COMPILE: GILOnceCell<Py<PyAny>> = GILOnceCell::new();
    static EXEC: GILOnceCell<Py<PyAny>> = GILOnceCell::new();

    let _ = column;

    #[allow(clippy::expect_used)] // failure is a Python bug
    let compile = COMPILE
        .import(py, "builtins", "compile")
        .expect("Python does not provide a compile() function");
    #[allow(clippy::expect_used)] // failure is a Python bug
    let exec = EXEC
        .import(py, "builtins", "exec")
        .expect("Python does not provide an exec() function");

    let mut code = String::with_capacity((line as usize) + RAISE.len());
    for _ in 1..line {
        code.push('\n');
    }
    code.push_str(RAISE);

    #[allow(clippy::expect_used)] // failure is a Python bug
    let code = compile
        .call1((code, file, intern!(py, "exec")))
        .expect("failed to compile PyErr location helper");
    #[allow(clippy::expect_used)] // failure is a Python bug
    let globals = [(intern!(py, "err"), err)]
        .into_py_dict(py)
        .expect("failed to create a dict(err=...)");

    #[allow(clippy::expect_used)] // failure is a Python bug
    let err = exec.call1((code, globals)).expect_err("raise must raise");
    err
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn python_cause() {
        Python::with_gil(|py| {
            let err = py
                .run(
                    &std::ffi::CString::new(
                        r#"
try:
    try:
        raise Exception("source")
    except Exception as err:
        raise IndexError("middle") from err
except Exception as err:
    raise LookupError("top") from err
"#,
                    )
                    .unwrap(),
                    None,
                    None,
                )
                .expect_err("raise must raise");

            let err = PyErrChain::new(py, err);
            assert_eq!(format!("{err}"), "LookupError: top");

            let err = err.source().expect("must have source");
            assert_eq!(format!("{err}"), "IndexError: middle");

            let err = err.source().expect("must have source");
            assert_eq!(format!("{err}"), "Exception: source");

            assert!(err.source().is_none());
        })
    }

    #[test]
    fn rust_source() {
        #[derive(Debug)]
        struct MyErr {
            msg: &'static str,
            source: Option<Box<Self>>,
        }

        impl fmt::Display for MyErr {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                fmt.write_str(self.msg)
            }
        }

        impl Error for MyErr {
            fn source(&self) -> Option<&(dyn Error + 'static)> {
                match &self.source {
                    None => None,
                    Some(source) => Some(&**source as &dyn Error),
                }
            }
        }

        Python::with_gil(|py| {
            let err = PyErrChain::new(
                py,
                MyErr {
                    msg: "top",
                    source: Some(Box::new(MyErr {
                        msg: "middle",
                        source: Some(Box::new(MyErr {
                            msg: "source",
                            source: None,
                        })),
                    })),
                },
            );

            let source = err.source().expect("must have source");
            let source = source.source().expect("must have source");
            assert!(source.source().is_none());

            let err = PyErr::from(err);
            assert_eq!(format!("{err}"), "Exception: top");

            let err = err.cause(py).expect("must have cause");
            assert_eq!(format!("{err}"), "Exception: middle");

            let err = err.cause(py).expect("must have cause");
            assert_eq!(format!("{err}"), "Exception: source");

            assert!(err.cause(py).is_none());
        })
    }

    #[test]
    fn err_location() {
        Python::with_gil(|py| {
            let err = err_with_location(py, PyException::new_err("oh no"), "foo.rs", 27, 15);

            // check the message, location traceback, and cause for the root error
            assert_eq!(format!("{err}"), "Exception: oh no");
            assert_eq!(
                err.traceback(py)
                    .expect("must have traceback")
                    .format()
                    .expect("traceback must be formattable"),
                r#"Traceback (most recent call last):
  File "foo.rs", line 27, in <module>
"#,
            );
            assert!(err.cause(py).is_none());

            // add an extra level of location traceback to the root error
            let err = err_with_location(py, err, "bar.rs", 24, 18);

            // create a new top-level error, caused by the root error
            let top = PyException::new_err("oh yes");
            top.set_cause(py, Some(err));
            let err = err_with_location(py, top, "baz.rs", 41, 1);

            // check the message and location traceback for the top-level error
            assert_eq!(format!("{err}"), "Exception: oh yes");
            assert_eq!(
                err.traceback(py)
                    .expect("must have traceback")
                    .format()
                    .expect("traceback must be formattable"),
                r#"Traceback (most recent call last):
  File "baz.rs", line 41, in <module>
"#,
            );

            // ensure that the top-level error has a cause
            let cause = err.cause(py).expect("must have a cause");

            // check the message, extended location traceback, and cause for the root error
            assert_eq!(format!("{cause}"), "Exception: oh no");
            assert_eq!(
                cause
                    .traceback(py)
                    .expect("must have traceback")
                    .format()
                    .expect("traceback must be formattable"),
                r#"Traceback (most recent call last):
  File "bar.rs", line 24, in <module>
  File "foo.rs", line 27, in <module>
"#,
            );
            assert!(cause.cause(py).is_none());
        })
    }

    #[test]
    fn anyhow() {
        Python::with_gil(|py| {
            let err = anyhow::anyhow!("source").context("middle").context("top");

            let err = PyErrChain::new(py, err);
            assert_eq!(format!("{err}"), "Exception: top");

            let err = err.source().expect("must have source");
            assert_eq!(format!("{err}"), "Exception: middle");

            let err = err.source().expect("must have source");
            assert_eq!(format!("{err}"), "Exception: source");

            assert!(err.source().is_none());
        })
    }
}
