use crate::align::*;
use crate::intrinsic::*;
use crate::parser::MarkerKind;
use crate::resource::*;
use crate::scopes::*;
use crate::types::*;

use std::alloc::{alloc, dealloc, Layout};
use std::collections::HashMap;

pub type Value = smallvec::SmallVec<[u8; 8]>;

#[derive(Debug)]
struct Stack {
    buffer: *mut u8,
    buffer_max: *mut u8,
    head: *mut u8,
    member_sizes: Vec<usize>,
}

impl Stack {
    fn new() -> Self {
        let stack_layout = Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap();
        let stack_ptr: *mut u8 = unsafe { alloc(stack_layout) };

        Stack {
            buffer: stack_ptr,
            buffer_max: unsafe { stack_ptr.add(STACK_SIZE) },
            head: stack_ptr,
            member_sizes: Vec::new(),
        }
    }

    fn push_zero(&mut self) {
        self.push_uninit(0);
    }

    fn push(&mut self, value: *const u8, size: usize) -> *mut u8 {
        let buffer = self.push_uninit(size);

        // SAFETY: This is safe even if the size is zero, because push_uninit will always
        // return a properly aligned, non-null pointer and that is all that is required for
        // copy to be safe when the size is 0.
        unsafe {
            std::ptr::copy(value, buffer, size);
        }

        buffer
    }

    /// Allocates a value of size bytes and returns the pointer to it.
    /// Intended to be used when you want to initialize the data in the buffer
    /// later.
    ///
    /// Returns a dangling pointer with STACK_ALIGN alignment if the size is zero
    fn push_uninit(&mut self, size: usize) -> *mut u8 {
        println!("+ {} bytes", size);

        self.member_sizes.push(size);
        if size == 0 {
            return STACK_ALIGN as *mut u8;
        }

        assert!(
            self.head as usize + size < self.buffer_max as usize,
            "Stack overflow"
        );

        let pos = self.head;

        unsafe {
            self.head = self.head.add(to_aligned(STACK_ALIGN, size));
        }

        pos
    }

    /// Makes sure there is enough space for size elements, and returns the head of the
    /// stack.
    ///
    /// SAFETY: Make sure to not use the storage after any writes have happened to the stack,
    /// such as push. push_uninit(as long as you don't write it yourself) and pop are fine though.
    fn temp_storage(&mut self, size: usize) -> *mut u8 {
        assert!(
            self.head as usize + size < self.buffer_max as usize,
            "Stack overflow"
        );

        self.head
    }

    fn pop(&mut self) -> (*const u8, usize) {
        let size = self.member_sizes.pop().unwrap();
        println!("- {} bytes", size);
        if size == 0 {
            return (std::ptr::NonNull::dangling().as_ptr(), 0);
        }

        unsafe {
            self.head = self.head.sub(to_aligned(STACK_ALIGN, size));
            (self.head, size)
        }
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        unsafe {
            dealloc(
                self.buffer,
                Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap(),
            );
        }
    }
}

const STACK_SIZE: usize = 2048;
const STACK_ALIGN: usize = 16;

struct Interpreter<'a> {
    stack: Stack,
    locals_stack: Stack,
    // TODO: Make the locals represented by their idex in the locals array so that this can be done
    // more efficiently.
    #[allow(unused)]
    locals: Vec<(ScopeMemberId, *mut u8)>,
    code: Vec<(&'a Ast, usize)>,
}

impl<'a> Interpreter<'a> {
    #[allow(unused)]
    pub fn new() -> Self {
        Interpreter {
            stack: Stack::new(),
            locals_stack: Stack::new(),
            locals: Vec::new(),
            code: Vec::new(),
        }
    }

    #[allow(unused)]
    fn get_local(&self, local_id: ScopeMemberId) -> *mut u8 {
        let &(_, ptr) = self
            .locals
            .iter()
            .rev()
            .find(|&&(id, _)| id == local_id)
            .unwrap();
        ptr
    }

    pub fn resume(
        &mut self,
        _resources: &Resources,
        _types: &Types,
        _scopes: &Scopes,
    ) -> Result<Value, Dependency> {
        let (ast, member_index) = self.code.pop().expect("Nothing to resume");

        while let Some(_) = ast.nodes.get(member_index) {
            // match member {}
        }

        for _ in ast.locals.all_locals.iter() {
            self.locals_stack.pop();
        }

        let (buffer_raw_ptr, buffer_raw_len) = self.stack.pop();
        let buffer = unsafe { std::slice::from_raw_parts(buffer_raw_ptr, buffer_raw_len).into() };

        Ok(buffer)
    }

    #[allow(unused)]
    pub fn interpret(
        &mut self,
        resources: &Resources,
        types: &Types,
        scopes: &Scopes,
        ast: &'a Ast,
    ) -> Result<Value, Dependency> {
        self.code.push((ast, 0));

        for &local_var_id in ast.locals.all_locals.iter() {
            let member = scopes.member(local_var_id);
            let type_handle = types.handle(member.type_.unwrap());
            self.locals_stack.push_uninit(type_handle.size);
        }

        self.resume(resources, types, scopes)
    }
}

pub fn interpret(resources: &Resources, types: &Types, scopes: &Scopes, ast: &Ast) -> Value {
    let mut stack = Stack::new();

    // Calculate storage locations, and stack position of all the locals.
    // TODO: This should also be moved out
    let mut locals = HashMap::with_capacity(ast.locals.all_locals.len());
    let mut local_size = 0;
    for &local_var_id in ast.locals.all_locals.iter() {
        let member = scopes.member(local_var_id);
        let type_handle = types.handle(member.type_.unwrap());
        local_size = to_aligned(type_handle.align, local_size);
        locals.insert(local_var_id, (local_size, type_handle.size));
        local_size += type_handle.size;
    }
    // TODO: Initializing this is unnecessary.
    let mut local_data = vec![0u8; to_aligned(STACK_ALIGN, local_size)];

    // Run the program
    let mut node_id = 0;
    while let Some(node) = ast.nodes.get(node_id) {
        node_id += 1;

        // TODO: Include enough information in the Ast to not have to rely on the runtime
        // to keep track of the size of values.
        match node.kind {
            NodeKind::Marker(MarkerKind::IfCondition(_, label_id)) => {
                // The size of a boolean is 1.
                let (condition, size) = stack.pop();
                assert_eq!(size, 1);

                if unsafe { *condition } == 0 {
                    node_id = *ast.label_map.get(&label_id).unwrap();
                }
            }
            NodeKind::Marker(MarkerKind::IfElseTrueBody {
                contains: _,
                true_body_label: _,
                false_body_label,
            }) => {
                node_id = *ast.label_map.get(&false_body_label).unwrap();
            }
            NodeKind::Marker(MarkerKind::LoopHead(_)) => {}
            NodeKind::MemberAccess { offset, size } => {
                let (value, length) = stack.pop();
                assert!(offset + size <= length);
                stack.push(unsafe { value.add(offset) }, size);
            }
            NodeKind::Constant(ref buffer) => {
                stack.push(buffer.as_ptr(), buffer.len());
            }
            NodeKind::IntrinsicTwo(intrinsic_kind) => {
                let (right, right_len) = stack.pop();
                let (left, left_len) = stack.pop();
                let mut output = 0;
                run_intrinsic_two(
                    intrinsic_kind,
                    &mut output,
                    unsafe { std::slice::from_raw_parts(left, left_len) },
                    unsafe { std::slice::from_raw_parts(right, right_len) },
                );

                stack.push(
                    &output as *const u64 as *const u8,
                    types.handle(node.type_).size,
                );
            }
            NodeKind::ScopeMemberReference(member_id) => match scopes.member(member_id).kind {
                ScopeMemberKind::LocalVariable => {
                    let &(pos, _size) = locals.get(&member_id).unwrap();
                    let bytes = (local_data.as_mut_ptr().wrapping_add(pos) as usize).to_le_bytes();
                    stack.push(bytes.as_slice().as_ptr(), 8);
                }
                ref kind => panic!("Unhandled identifier kind {:?}", kind),
            },
            NodeKind::Identifier(member_id) => match scopes.member(member_id).kind {
                ScopeMemberKind::LocalVariable => {
                    let &(pos, size) = locals.get(&member_id).unwrap();

                    stack.push(local_data.as_ptr().wrapping_add(pos), size);
                }
                ref kind => panic!("Unhandled identifier kind {:?}", kind),
            },
            NodeKind::BitCast => {}
            NodeKind::Assign => {
                let (value, value_len) = stack.pop();
                let (pointer, pointer_len) = stack.pop();

                if value_len > 0 {
                    assert_eq!(pointer_len, 8);

                    unsafe {
                        std::ptr::copy(value, *(pointer as *mut *mut u8), value_len);
                    }

                    stack.push(value, value_len);
                }
            }
            NodeKind::Resource(id) => {
                let resource = resources.resource(id);
                match resource.kind {
                    ResourceKind::Done(ref value, ref pointers) => {
                        let mut value_copy = value.clone();

                        for &(sub_offset, sub_id, _) in pointers {
                            match resources.resource(sub_id).kind {
                                ResourceKind::Done(ref sub_value, ref sub_pointers) => {
                                    if sub_pointers.len() > 0 {
                                        panic!("Cannot copy a resource with recursive subpointers");
                                    }

                                    value_copy[sub_offset..sub_offset + 8].copy_from_slice(
                                        &(sub_value.as_ptr() as usize).to_le_bytes(),
                                    );
                                }
                                _ => {
                                    todo!("We can't currently deal with non-finished resources");
                                }
                            }
                        }

                        stack.push(value_copy.as_ptr(), value_copy.len());
                    }
                    _ => {
                        todo!("We can't currently deal with non-finished resources");
                    }
                }
            }
            NodeKind::FunctionCall(_) => todo!(),
            NodeKind::Dereference => {
                let (pointer, pointer_len) = stack.pop();
                assert_eq!(pointer_len, 8);

                stack.push(
                    unsafe { *(pointer as *mut *mut u8) },
                    types.handle(node.type_).size,
                );
            }
            NodeKind::If(_) => {}
            NodeKind::IfWithElse { end_label: _ } => {}
            NodeKind::Loop(head, _) => node_id = *ast.label_map.get(&head).unwrap(),
            NodeKind::Struct => match types.get(node.type_).kind {
                TypeKind::Struct { ref members } => {
                    let handle = types.handle(node.type_);
                    let temp = stack.temp_storage(handle.size);

                    for &(_, offset, member_type_handle) in members.iter().rev() {
                        let (value_buffer, value_size) = stack.pop();
                        assert_eq!(value_size, member_type_handle.size);

                        unsafe {
                            std::ptr::copy(value_buffer, temp.add(offset), member_type_handle.size);
                        }
                    }

                    stack.push(temp, handle.size);
                }
                _ => unreachable!("A Struct node has to have to type of struct"),
            },
            NodeKind::Declaration { variable_name } => {
                let &(pos, size) = locals.get(&variable_name).unwrap();
                let (pointer, pointer_size) = stack.pop();
                assert_eq!(size, pointer_size);

                unsafe {
                    std::ptr::copy(pointer, local_data.as_mut_ptr().add(pos), size);
                }

                stack.push_zero();
            }
            NodeKind::Block {
                ref contents,
                label: _,
            } => {
                let (return_value, return_value_length) = stack.pop();
                for _ in contents[1..].iter() {
                    stack.pop();
                }

                stack.push(return_value, return_value_length);
            }
            NodeKind::Skip { label } => {
                node_id = *ast.label_map.get(&label).unwrap();
            }
        }
    }

    let (buffer_raw_ptr, buffer_raw_len) = stack.pop();
    let buffer = unsafe { std::slice::from_raw_parts(buffer_raw_ptr, buffer_raw_len).into() };

    buffer
}
