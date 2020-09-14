use crate::id::IdVec;

pub type ConstBuffer = smallvec::SmallVec<[u8; 8]>;

/// A Value is either a LocalHandle, or a Constant.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
	Local(LocalHandle),
	Constant(ConstBuffer),
}

impl From<usize> for Value {
	fn from(other: usize) -> Self {
		Self::Constant(ConstBuffer::from_slice(&other.to_le_bytes()))
	}
}

impl From<u64> for Value {
	fn from(other: u64) -> Self {
		Self::Constant(ConstBuffer::from_slice(&other.to_le_bytes()))
	}
}

impl From<i64> for Value {
	fn from(other: i64) -> Self {
		Self::Constant(ConstBuffer::from_slice(&other.to_le_bytes()))
	}
}

impl From<u32> for Value {
	fn from(other: u32) -> Self {
		Self::Constant(ConstBuffer::from_slice(&other.to_le_bytes()))
	}
}

impl From<i32> for Value {
	fn from(other: i32) -> Self {
		Self::Constant(ConstBuffer::from_slice(&other.to_le_bytes()))
	}
}

/// A handle to any subsection of a local.
///
/// It cannot however contain a constant value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LocalHandle {
	offset: usize,
	// TODO: Check if align is really necessary to have as a member here.
	align: usize,
	pub size: usize,
	id: LocalId,
}

create_id!(LocalId);

struct Local {
	size: usize,
	align: usize,
}

pub struct Locals {
	locals: IdVec<Local, LocalId>,
}

impl Locals {
	pub fn new() -> Self {
		Self {
			locals: IdVec::new(),
		}
	}

	/// Allocates the space of a type as a local.
	pub fn allocate(&mut self, type_: crate::types::TypeHandle) -> LocalHandle {
		let id = self.locals.push(Local {
			size:  type_.size,
			align: type_.align,
		});

		LocalHandle {
			id,
			offset: 0,
			size:  type_.size,
			align: type_.align,
		}
	}

	pub fn id_as_handle(&self, id: LocalId) -> LocalHandle {
		let local = self.locals.get(id);

		LocalHandle {
			size: local.size,
			align: local.align,
			offset: 0,
			id,
		}
	}

	pub fn layout(&self) -> StackFrameLayout {
		let mut total_size = 0;
		let mut local_positions = Vec::with_capacity(self.locals.len());

		for local in self.locals.iter() {
			total_size = crate::align::to_aligned(local.align, total_size);

			local_positions.push(total_size);
			total_size += local.size;
		}

		StackFrameLayout {
			total_size,
			local_positions,
		}
	}
}

// TODO: Add a special system for function arguments to make them less jank.
/// A stack frame layout maps from local ids to locations in the stack frame.
pub struct StackFrameLayout {
	total_size: usize,
	local_positions: Vec<usize>,
}

impl StackFrameLayout {
	fn local_pos_and_size(&self, local: LocalHandle) -> (usize, usize) {
		(
			self.local_positions[local.id.into_index()] + local.offset,
			local.size,
		)
	}

	pub fn create_instance_with_func_args<'a>(
		self: &std::sync::Arc<Self>,
		mut args: impl Iterator<Item = (usize, &'a [u8])> + 'a,
	) -> StackFrameInstance {
		let mut instance = StackFrameInstance {
			buffer: vec![ForceAlignment([0; STACK_FRAME_ALIGNMENT]); self.total_size],
			layout: self.clone(),
		};

		for (offset, value) in args {
			instance.insert_into_index(offset, value);
		}

		instance
	}

	pub fn create_instance(self: &std::sync::Arc<Self>) -> StackFrameInstance {
		StackFrameInstance {
			buffer: vec![ForceAlignment([0; STACK_FRAME_ALIGNMENT]); self.total_size],
			layout: self.clone(),
		}
	}
}

const STACK_FRAME_ALIGNMENT: usize = std::mem::size_of::<ForceAlignment>();

#[repr(align(8))]
#[derive(Clone, Copy)]
struct ForceAlignment([u8; 8]);

pub struct StackFrameInstance {
	/// The buffer for the data inside. The type here is kindof weird, but the reason for it is
	/// so that we force it to be aligned to the right number of bytes, so that nothing in the
	/// stack itself becomes unaligned.
	buffer: Vec<ForceAlignment>,

	layout: std::sync::Arc<StackFrameLayout>,
}

impl StackFrameInstance {
	pub fn get_u32(&self, value: &Value) -> u32 {
		match value {
			Value::Local(handle) => {
				let (pos, size) = self.layout.local_pos_and_size(*handle);
				debug_assert_eq!(size, 4);
				debug_assert!(crate::align::is_aligned(4, pos));

				// SAFETY: The position should be aligned to 4 bytes.
				unsafe {
					*(&self.buffer_bytes()[pos] as *const u8 as *const u32)
				}
			}
			Value::Constant(vector) => {
				if let &[a, b, c, d] = vector.as_slice() {
					u32::from_le_bytes([a, b, c, d])
				} else {
					panic!("Cannot call get_u64 with non 64 bit value");
				}
			}
		}
	}

	/// Returns a u64. Panics if the value is invalid.
	pub fn get_u64(&self, value: &Value) -> u64 {
		match value {
			Value::Local(handle) => {
				let (pos, size) = self.layout.local_pos_and_size(*handle);
				debug_assert_eq!(size, 8);
				debug_assert!(crate::align::is_aligned(8, pos));

				// SAFETY: The position should be aligned to 8 bytes.
				unsafe {
					*(&self.buffer_bytes()[pos] as *const u8 as *const u64)
				}
			}
			Value::Constant(vector) => {
				if let &[a, b, c, d, e, f, g, h] = vector.as_slice() {
					u64::from_le_bytes([a, b, c, d, e, f, g, h])
				} else {
					panic!("Cannot call get_u64 with non 64 bit value");
				}
			}
		}
	}

	pub fn clone_value(&self, value: &Value) -> ConstBuffer {
		match value {
			Value::Local(local) => {
				let (pos, size) = self.layout.local_pos_and_size(*local);
				ConstBuffer::from_slice(&self.buffer_bytes()[pos..pos + size])
			}
			Value::Constant(vector) => vector.clone(),
		}
	}

	pub fn get_value<'a>(&'a self, value: &'a Value) -> &'a [u8] {
		match value {
			Value::Local(local) => {
				let (pos, size) = self.layout.local_pos_and_size(*local);
				&self.buffer_bytes()[pos..pos + size]
			}
			Value::Constant(vector) => vector.as_slice(),
		}
	}

	pub fn insert_value_into_local(&mut self, local: LocalHandle, value: &Value) {
		match value {
			Value::Local(from_local) => {
				let (to_pos, to_size) = self.layout.local_pos_and_size(local);
				let (from_pos, from_size) = self.layout.local_pos_and_size(*from_local);
				assert_eq!(from_size, to_size);

				self.buffer_bytes_mut().copy_within(from_pos..from_pos + from_size, to_pos);
			}
			Value::Constant(ref values) => 
				self.insert_into_local(local, values),
		}
	}

	/// Inserts a buffer of data into a local.
	///
	/// # Panics
	/// If the data is not the same size as the local
	pub fn insert_into_local(&mut self, local: LocalHandle, data: &[u8]) {
		let (pos, size) = self.layout.local_pos_and_size(local);
		self.buffer_bytes_mut()[pos..pos + size].copy_from_slice(data);
	}

	pub fn insert_into_index(&mut self, index: usize, data: &[u8]) {
		self.buffer_bytes_mut()[index..index + data.len()].copy_from_slice(data);
	}

	fn buffer_bytes(&self) -> &[u8] {
		let slice_ptr = self.buffer.as_ptr();

		// SAFETY:
		// slice_ptr is aligned to a u8 properly, and isn't null(because it came from a slice).
		//
		// slice_ptr also lives for as long as the slice we return, because it came from the input
		// slice, which lives for at least as long as the slice we output.
		//
		// We also know that the pointer allocation is at least as big as self.buffer.len() * ...
		unsafe {
			std::slice::from_raw_parts(
				slice_ptr as *const u8, 
				self.buffer.len() * std::mem::size_of::<ForceAlignment>()
			)
		}
	}

	fn buffer_bytes_mut(&mut self) -> &mut [u8] {
		let slice_ptr = self.buffer.as_mut_ptr();

		// SAFETY:
		// This is safe for the exact same reasons buffer_bytes is safe.
		//
		// Also, there will not ever be two mutable references to the buffer because that would
		// require two mutable references to self.
		unsafe {
			std::slice::from_raw_parts_mut(
				slice_ptr as *mut u8, 
				self.buffer.len() * std::mem::size_of::<ForceAlignment>()
			)
		}
	}
}
