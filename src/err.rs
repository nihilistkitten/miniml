//! Implements the `MlError` type.

use thiserror::Error;

use crate::parse::ParserError;

#[derive(Debug, Error)]
pub enum MlError {
    #[error("{0}")]
    ParseError(#[from] ParserError),
}

pub type MlResult<T> = Result<T, MlError>;
