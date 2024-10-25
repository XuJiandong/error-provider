extern crate alloc;
use crate::error::Error;
use alloc::boxed::Box;
use core::fmt;

#[derive(Debug)]
pub enum ReadExactError {
    ReadExactEof,
}

impl fmt::Display for ReadExactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReadExactError::ReadExactEof => write!(f, "Read exact EOF error"),
        }
    }
}

impl Error for ReadExactError {
    fn provide<'a>(&'a self, request: &mut crate::error::Request<'a>) {
        request.provide_ref(self);
    }
}

pub trait Read {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Box<dyn Error>>;
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Box<dyn Error>>;
}

impl Read for &[u8] {
    #[inline]
    fn read(&mut self, _buf: &mut [u8]) -> Result<usize, Box<dyn Error>> {
        unimplemented!()
    }
    fn read_exact(&mut self, _buf: &mut [u8]) -> Result<(), Box<dyn Error>> {
        // return error for demo purpose
        Err(Box::new(ReadExactError::ReadExactEof))
    }
}

#[test]
fn test_read_exact() {
    let mut buf = [0u8; 10];
    let data = [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let err = (&data[..]).read_exact(&mut buf);
    assert!(err.is_err());
    let err = err.err().unwrap();
    // demonstrate how to infer concrete error type from `Error` trait
    let dyn_error = err.as_ref() as &dyn Error;
    let error_ref = crate::error::request_ref::<ReadExactError>(dyn_error).unwrap();
    assert!(matches!(error_ref, ReadExactError::ReadExactEof));
}
