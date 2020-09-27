use std::sync::{ Arc, Mutex };

use crate::resource::*;
use crate::code_loc::*;
use crate::print_location;

lazy_static! {
	static ref LOGGER: Arc<Mutex<LoggerInternal>> = Arc::new(Mutex::new(LoggerInternal {
		info_cache: Vec::new(),
		errors: Vec::new(),
		warnings: Vec::new(),
	}));
}

pub fn print_output(resources: &Resources) {
	let mut logger = LOGGER.lock().unwrap();

	if logger.errors.len() > 0 {
		print_message_list(
			"ERROR", 
			resources,
			logger.errors.iter().map(|Error(info, message)| (info.as_slice(), message))
		);
	} else {
		print_message_list(
			"WARNING", 
			resources,
			logger.warnings.iter().map(|Warning(info, message)| (info.as_slice(), message))
		);
	}

	logger.errors.clear();
	logger.warnings.clear();
}

fn print_message_list<'a>(
	name: &'a str,
	resources: &Resources,
	messages: impl Iterator<Item = (&'a [Message], &'a Message)>
) {
	let mut is_first = true;
	for (info, message) in messages {
		if !is_first {
			println!();
		}
		is_first = false;

		println!("{} at {:?}: {}", name, message.source_code_location, message.message);

		let file = message.source_code_location.file;
		if let Some(code) = resources.code_cache.get(&file) {
			print_location(code, &message.source_code_location, "");
		} else {
			println!("File does not exist!");
		}

		for info in info {
			if info.source_code_location.file != file {
				println!("{:?}", info.source_code_location);
			}

			if let Some(code) = resources.code_cache.get(&file) {
				print_location(code, &info.source_code_location, &info.message);
			} else {
				println!("File does not exist!");
			}
		}

		println!("  compiler: {:?}", message.compiler_location);
	}
}

pub fn info(message: Message) {
	let mut logger = LOGGER.lock().unwrap();
	logger.info_cache.push(message);
}

pub fn error(mut error: Error) {
	let mut logger = LOGGER.lock().unwrap();

	error.0.append(&mut logger.info_cache);
	logger.errors.push(error);
}

pub fn warning(mut warning: Warning) {
	let mut logger = LOGGER.lock().unwrap();

	warning.0.append(&mut logger.info_cache);
	logger.warnings.push(warning);
}

struct LoggerInternal {
	info_cache: Vec<Message>,
	errors: Vec<Error>,
	warnings: Vec<Warning>,
}

#[derive(Debug)]
pub struct Error(pub Vec<Message>, pub Message);
pub struct Warning(pub Vec<Message>, pub Message);

#[derive(Debug)]
pub struct Message {	
	pub message: String,
	pub source_code_location: CodeLoc,
	pub compiler_location: CodeLoc,
}

macro_rules! info {
	($location:expr, $($format_message:tt)+) => {{
		info(Message {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { 
				line: line!(), 
				column: column!(), 
				file: ustr::ustr(file!()),
			},
		});
	}}
}

macro_rules! warning {
	($location:expr, $($format_message:tt)+) => {{
		warning(Warning(Vec::new(), Message {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { 
				line: line!(), 
				column: column!(), 
				file: ustr::ustr(file!()),
			},
		}));
	}}
}

macro_rules! error {
	($location:expr, $($format_message:tt)+) => {{
		error(Error(Vec::new(), Message {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { 
				line: line!(), 
				column: column!(), 
				file: ustr::ustr(file!()),
			},
		}));

		Err(())
	}}
}

macro_rules! error_value {
	($location:expr, $($format_message:tt)+) => {{
		error(Error(Vec::new(), Message {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { 
				line: line!(), 
				column: column!(), 
				file: ustr::ustr(file!()),
			},
		}));

		()
	}}
}
