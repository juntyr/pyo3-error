//! [![CI Status]][workflow] [![MSRV]][repo] [![Latest Version]][crates.io] [![Rust Doc Crate]][docs.rs] [![Rust Doc Main]][docs]
//!
//! [CI Status]: https://img.shields.io/github/actions/workflow/status/juntyr/pyo3-error/ci.yml?branch=main
//! [workflow]: https://github.com/juntyr/pyo3-error/actions/workflows/ci.yml?query=branch%3Amain
//!
//! [MSRV]: https://img.shields.io/badge/MSRV-1.76.0-blue
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

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
