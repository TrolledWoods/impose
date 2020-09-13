use crate::types::{ TypeHandle };

#[derive(PartialEq, Eq)]
pub struct StackMember(TypeHandle, usize);

pub struct StackFrameAllocator {
	stack_pointer: usize,
}

impl StackFrameAllocator {
	pub fn new() -> Self {
		Self {
			stack_pointer: 0,
		}
	}

	pub fn allocate(&mut self, type_: TypeHandle) -> StackMember {
		// Align the stack pointer
		while self.stack_pointer & (type_.align - 1) != 0 {
			self.stack_pointer += 1;
		}

		let position = self.stack_pointer;
		self.stack_pointer += type_.size;

		StackMember(type_, position)
	}

	pub fn create_instance(&self) -> StackFrameInstance {
		StackFrameInstance {
			buffer: vec![
				ForceAlignment([0xff; STACK_FRAME_ALIGNMENT]);
				1 + self.stack_pointer / STACK_FRAME_ALIGNMENT
			].into_boxed_slice()
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
	buffer: Box<[ForceAlignment]>,
}

impl StackFrameInstance {
	/// Returns a primitive stack member(you shouldn't try to get anything else with this, as
	/// the memory layout will get so complicated if you do).
	///
	/// # SAFETY
	/// Make sure that member location is aligned properly to its alignment, 
	/// and that it isn't out of bounds.
	///
	/// The alignment of T should also not be greater than STACK_FRAME_ALIGNMENT. If it has to be,
	/// then change STACK_FRAME_ALIGNMENT to something bigger.
	pub unsafe fn get_primitive_member<T: Copy>(&self, member: StackMember) -> T {
		debug_assert!(std::mem::align_of::<T>() <= STACK_FRAME_ALIGNMENT, "Too big alignment");
		debug_assert_eq!(member.1 % std::mem::align_of::<T>(), 0, "Bad alignment");

		// SAFETY: The member should be aligned properly according to T's alignment
		// (and its alignment should be smaller than the STACK_FRAME_ALIGNMENT). 
		// If it is, then since buffer_bytes returns a slice aligned to STACK_FRAME_ALIGNMENT,
		// everything should be fine.
		// Also, the members location shouldn't be out of bounds
		unsafe {
			*(self.buffer_bytes()[member.1] as *const u8 as *const T)
		}
	}

	/// Returns a mutable reference to a primitive stack member
	/// (you shouldn't try to get anything else with this, as the memory layout will get so 
	/// complicated if you do).
	///
	/// # SAFETY
	/// Make sure that member location is aligned properly to its alignment, 
	/// and that it isn't out of bounds.
	///
	/// The alignment of T should also not be greater than STACK_FRAME_ALIGNMENT. If it has to be,
	/// then change STACK_FRAME_ALIGNMENT to something bigger.
	pub unsafe fn get_primitive_member_mut<T: Copy>(&mut self, member: StackMember) -> &mut T {
		debug_assert!(std::mem::align_of::<T>() <= STACK_FRAME_ALIGNMENT, "Too big alignment");
		debug_assert_eq!(member.1 % std::mem::align_of::<T>(), 0, "Bad alignment");

		// SAFETY: The member should be aligned properly according to T's alignment
		// (and its alignment should be smaller than the STACK_FRAME_ALIGNMENT). 
		// If it is, then since buffer_bytes returns a slice aligned to STACK_FRAME_ALIGNMENT,
		// everything should be fine.
		// Also, the members location shouldn't be out of bounds
		unsafe {
			&mut *(self.buffer_bytes_mut()[member.1] as *mut u8 as *mut T)
		}
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
