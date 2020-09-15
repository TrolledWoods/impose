use crate::id::*;
use crate::align::*;

pub type ConstBuffer = smallvec::SmallVec<[u8; 8]>;

/// A Value is either a LocalHandle, or a Constant.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
	Local(LocalHandle),
	Pointer {
		pointer: LocalId,
		pointer_offset: usize,
		offset: usize,
		// TODO: This is not really necessary, but we have it here
		// for now, because we do not always know the sizes we want in
		// operations currently.
		resulting_size: usize,
	},
	Constant(ConstBuffer),
}

impl Value {
	pub fn get_sub_value(&self, offset: usize, size: usize, align: usize) -> Value {
		match *self {
			Value::Local(handle) => {
				debug_assert!(offset + size <= handle.size);

				// Check that our align is aligned if the handle is aligned.
				debug_assert!(is_aligned(align, handle.align));
				debug_assert!(is_aligned(align, offset));

				Value::Local(LocalHandle {
					offset: handle.offset + offset,
					// TODO: Check if align is really necessary to have as a member here.
					align,
					size,
					id: handle.id,
				})
			}
			Value::Pointer { pointer, pointer_offset, offset: p_offset, resulting_size } => {
				debug_assert!(offset + size <= resulting_size);
				debug_assert!(is_aligned(align, offset));

				Value::Pointer {
					pointer: pointer,
					pointer_offset,
					offset: p_offset + offset,
					resulting_size: size,
				}
			}
			Value::Constant(ref buffer) => {
				// Align here doesn't matter
				Value::Constant(ConstBuffer::from(&buffer[offset..offset + size]))
			}
		}
	}
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

impl LocalHandle {
	/// Turns the local into an indirect value pointing to that local.
	pub fn dereference_into_pointer_value(&self) -> Value {
		Value::Pointer {
			pointer: self.id,
			pointer_offset: self.offset,
			offset: 0,
			resulting_size: self.size,
		}
	}
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

	pub fn layout(&self) -> StackFrameLayout {
		let mut total_size = 0;
		let mut local_positions = Vec::with_capacity(self.locals.len());

		for local in self.locals.iter() {
			total_size = to_aligned(local.align, total_size);

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

	fn local_pos(&self, local: LocalId) -> usize {
		self.local_positions[local.into_index()]
	}

	pub fn create_instance_with_func_args<'a>(
		self: &std::sync::Arc<Self>,
		args: impl Iterator<Item = (usize, &'a [u8])> + 'a,
	) -> StackFrameInstance {
		let mut instance = StackFrameInstance {
			buffer: std::pin::Pin::new(vec![ForceAlignment([0; STACK_FRAME_ALIGNMENT]); self.total_size].into_boxed_slice()),
			layout: self.clone(),
		};

		for (offset, value) in args {
			instance.insert_into_index(offset, value);
		}

		instance
	}

	pub fn create_instance(self: &std::sync::Arc<Self>) -> StackFrameInstance {
		StackFrameInstance {
			buffer: std::pin::Pin::new(vec![ForceAlignment([0; STACK_FRAME_ALIGNMENT]); self.total_size].into_boxed_slice()),
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
	buffer: std::pin::Pin<Box<[ForceAlignment]>>,

	layout: std::sync::Arc<StackFrameLayout>,
}

impl StackFrameInstance {
	pub fn address_of_local(&self, local: LocalHandle) -> *const u8 {
		let (pos, _) = self.layout.local_pos_and_size(local);
		&self.bytes()[pos]
	}

	pub fn get_u32(&self, value: &Value) -> u32 {
		if let &[a, b, c, d] = self.get_value(value) {
			u32::from_le_bytes([a, b, c, d])
		} else {
			panic!("Cannot call get_u32 with non 32 bit value");
		}
	}

	/// Returns a u64. Panics if the value is invalid.
	pub fn get_u64(&self, value: &Value) -> u64 {
		if let &[a, b, c, d, e, f, g, h] = self.get_value(value) {
			u64::from_le_bytes([a, b, c, d, e, f, g, h])
		} else {
			panic!("Cannot call get_u64 with non 64 bit value");
		}
	}

	pub fn clone_value(&self, value: &Value) -> ConstBuffer {
		ConstBuffer::from(self.get_value(value))
	}

	pub fn get_value<'a>(&'a self, value: &'a Value) -> &'a [u8] {
		match *value {
			Value::Local(local) => {
				let (pos, size) = self.layout.local_pos_and_size(local);
				&self.bytes()[pos..pos + size]
			}
			Value::Pointer { pointer, pointer_offset, offset, resulting_size } => {
				let pointer_pos = self.layout.local_pos(pointer) + pointer_offset;
				let from = self.get_at_index::<*const u8>(pointer_pos).wrapping_add(offset);

				println!("PAUSE!!!!");

				// SAFETY: Non-existant. This is for my own language(unsafe), which means some
				// parts of the runtime has to be unsafe.
				//
				// TODO: Make sure that the &'a [u8] we are returning does not mutate while
				// reading it. This shouldn't be the case, but it might be.
				unsafe { std::slice::from_raw_parts(from, resulting_size) }
			}
			Value::Constant(ref vector) => vector.as_slice(),
		}
	}

	pub fn insert_value_into_local(&mut self, local: LocalHandle, value: &Value) {
		match *value {
			Value::Local(from_local) => {
				let (to_pos, to_size) = self.layout.local_pos_and_size(local);
				let (from_pos, from_size) = self.layout.local_pos_and_size(from_local);
				assert_eq!(from_size, to_size);

				self.bytes_mut().copy_within(from_pos..from_pos + from_size, to_pos);
			}
			Value::Pointer { pointer, pointer_offset, offset, resulting_size } => {
				let (to_pos, to_size) = self.layout.local_pos_and_size(local);
				let pointer_pos = self.layout.local_pos(pointer) + pointer_offset;

				assert!(to_size <= resulting_size);

				// We have to do these in this specific order, so that we do not have a &mut [u8]
				// and a &[u8] at the same time.
				let to_loc = &mut self.bytes_mut()[to_pos] as *mut u8;
				let from = self.get_at_index::<*const u8>(pointer_pos).wrapping_add(offset);

				// SAFETY: There is no safety. The programming language we are running is not a
				// safe programming language, which means it cannot by nature be safe.
				unsafe {
					std::ptr::copy(from, to_loc, to_size);
				}
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
		self.bytes_mut()[pos..pos + size].copy_from_slice(data);
	}

	/// Returns a value at the index.
	///
	/// # Panics
	/// Panics in debug mode if the index is not aligned to the alignment of the type,
	/// or if the alignment of the type is bigger than the max alignment.
	pub fn get_at_index<T>(&self, index: usize) -> T where T: Copy {
		debug_assert!(std::mem::align_of::<T>() <= STACK_FRAME_ALIGNMENT);
		debug_assert!(is_aligned(std::mem::align_of::<T>(), index));

		unsafe {
			*(&self.bytes()[index] as *const u8 as *const T)
		}
	}

	pub fn insert_into_index(&mut self, index: usize, data: &[u8]) {
		self.bytes_mut()[index..index + data.len()].copy_from_slice(data);
	}

	fn bytes(&self) -> &[u8] {
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

	fn bytes_mut(&mut self) -> &mut [u8] {
		let slice_ptr = self.buffer.as_mut_ptr();

		// SAFETY:
		// This is safe for the exact same reasons bytes is safe.
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
