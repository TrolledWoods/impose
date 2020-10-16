//!
//! Command line argument handling.
//!
use std::env;
use std::fmt;
use std::path::PathBuf;

pub enum Mode {
    TestFolder(PathBuf),
    CompileFile(PathBuf),
}

pub struct Config {
    pub executable_path: PathBuf,
    pub mode: Mode,
}

pub fn parse_arguments() -> Result<Config, Error> {
    let mut args = env::args();

    // The location of the executable.
    let executable_path = args.next().ok_or(Error::NoExecutablePath)?.into();

    // TODO: When no arguments are given, show a help output.
    // let file_path: PathBuf = args.next().ok_or(Error::NoFilePath)?.into();
    let file_path: PathBuf = args.next().unwrap_or_else(|| String::from("tests/")).into();

    Ok(Config {
        executable_path,
        mode: match file_path.is_dir() {
            true => Mode::TestFolder(file_path),
            false => Mode::CompileFile(file_path),
        },
    })
}

#[derive(Debug)]
pub enum Error {
    NoExecutablePath,
    #[allow(unused)]
    NoFilePath,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::NoExecutablePath => write!(f, "Couldn't find path to executable")?,
            Error::NoFilePath => {
                write!(f, "Expected a path to the file that's going to be compiled")?
            }
        }

        Ok(())
    }
}
