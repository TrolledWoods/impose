use crate::types::*;
use crate::operator::*;

fn is_primitive_int(id: TypeId) -> bool {
	match id {
		U8_TYPE_ID | U16_TYPE_ID | U32_TYPE_ID | U64_TYPE_ID |
		S8_TYPE_ID | S16_TYPE_ID | S32_TYPE_ID | S64_TYPE_ID => true,
		_ => false,
	}
}

#[derive(Debug, Clone, Copy)]
pub enum IntrinsicKindTwo {
	AddI,
	AddF64,
	AddF32,
	SubI,
	SubF64,
	SubF32,
	MulI,
	MulF64,
	MulF32,
	DivI,
	DivF64,
	DivF32,

	PointerAdd { size: u64 },
	PointerSub { size: u64 },
	PointerDiff { size: u64 },

	Equal,
	NotEqual,
	Less,
	LessEqu,
	Greater,
	GreaterEqu,

	BitAnd,
	BitXor,
	BitOr,
}

pub fn get_binary_operator_intrinsic(operator: Operator, types: &Types, left_type: TypeId, right_type: TypeId)
	-> Option<(IntrinsicKindTwo, TypeId)>
{
	Some(match (operator, left_type, right_type) {
		(Operator::Add, F64_TYPE_ID, F64_TYPE_ID) =>
			(IntrinsicKindTwo::AddF64, F64_TYPE_ID),
		(Operator::Add, F32_TYPE_ID, F32_TYPE_ID) =>
			(IntrinsicKindTwo::AddF32, F32_TYPE_ID),
		(Operator::Add, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::AddI, left),

		(Operator::Sub, F64_TYPE_ID, F64_TYPE_ID) =>
			(IntrinsicKindTwo::SubF64, F64_TYPE_ID),
		(Operator::Sub, F32_TYPE_ID, F32_TYPE_ID) =>
			(IntrinsicKindTwo::SubF32, F32_TYPE_ID),
		(Operator::Sub, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::SubI, left),

		(Operator::MulOrDeref, F64_TYPE_ID, F64_TYPE_ID) =>
			(IntrinsicKindTwo::MulF64, F64_TYPE_ID),
		(Operator::MulOrDeref, F32_TYPE_ID, F32_TYPE_ID) =>
			(IntrinsicKindTwo::MulF32, F32_TYPE_ID),
		(Operator::MulOrDeref, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::MulI, left),

		(Operator::Div, F64_TYPE_ID, F64_TYPE_ID) =>
			(IntrinsicKindTwo::DivF64, F64_TYPE_ID),
		(Operator::Div, F32_TYPE_ID, F32_TYPE_ID) =>
			(IntrinsicKindTwo::DivF32, F32_TYPE_ID),
		(Operator::Div, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::DivI, left),

		(Operator::Equ, BOOL_TYPE_ID, BOOL_TYPE_ID) =>
			(IntrinsicKindTwo::Equal, BOOL_TYPE_ID),
		(Operator::NEqu, BOOL_TYPE_ID, BOOL_TYPE_ID) =>
			(IntrinsicKindTwo::NotEqual, BOOL_TYPE_ID),

		(Operator::Equ, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::Equal, BOOL_TYPE_ID),
		(Operator::NEqu, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::NotEqual, BOOL_TYPE_ID),
		(Operator::Less, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::Less, BOOL_TYPE_ID),
		(Operator::LessEqu, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::LessEqu, BOOL_TYPE_ID),
		(Operator::Greater, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::Greater, BOOL_TYPE_ID),
		(Operator::GreaterEqu, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::GreaterEqu, BOOL_TYPE_ID),

		(Operator::BitAndOrPointer, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::BitAnd, left),
		(Operator::BitwiseOrOrLambda, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::BitOr, left),
		(Operator::BitXor, left, right) if is_primitive_int(left) && left == right =>
			(IntrinsicKindTwo::BitXor, left),

		(Operator::Add, left, U64_TYPE_ID) => {
			if let TypeKind::Pointer(internal) = types.get(left).kind {
				let size = types.handle(internal).size as u64;

				(IntrinsicKindTwo::PointerAdd { size }, left)
			} else {
				return None
			}
		}
		(Operator::Sub, left, U64_TYPE_ID) => {
			if let TypeKind::Pointer(internal) = types.get(left).kind {
				let size = types.handle(internal).size as u64;

				(IntrinsicKindTwo::PointerSub { size }, left)
			} else {
				return None
			}
		}
		(Operator::Sub, left, right) => {
			match (&types.get(left).kind, &types.get(right).kind) {
				(TypeKind::Pointer(left), TypeKind::Pointer(right)) if left == right => {
					let size = types.handle(*left).size as u64;

					(IntrinsicKindTwo::PointerDiff { size }, U64_TYPE_ID)
				}
				_ => return None,
			}
		}

		_ => return None,
	})
}

pub fn run_intrinsic_two(intrinsic: IntrinsicKindTwo, buf: &mut u64, a: &[u8], b: &[u8]) {
	match intrinsic {
		IntrinsicKindTwo::AddI   => *buf = buf_to_u64(a).wrapping_add(buf_to_u64(b)),
		IntrinsicKindTwo::AddF64 =>
			*buf = (f64::from_bits(buf_to_u64(a)) + f64::from_bits(buf_to_u64(b))).to_bits(),
		IntrinsicKindTwo::AddF32 =>
			*buf = (f32::from_bits(buf_to_u32(a)) + f32::from_bits(buf_to_u32(b))).to_bits() as u64,

		IntrinsicKindTwo::SubI   => *buf = buf_to_u64(a).wrapping_sub(buf_to_u64(b)),
		IntrinsicKindTwo::SubF64 =>
			*buf = (f64::from_bits(buf_to_u64(a)) - f64::from_bits(buf_to_u64(b))).to_bits(),
		IntrinsicKindTwo::SubF32 =>
			*buf = (f32::from_bits(buf_to_u32(a)) - f32::from_bits(buf_to_u32(b))).to_bits() as u64,

		IntrinsicKindTwo::DivI   => *buf = buf_to_u64(a) / buf_to_u64(b),
		IntrinsicKindTwo::DivF64 =>
			*buf = (f64::from_bits(buf_to_u64(a)) / f64::from_bits(buf_to_u64(b))).to_bits(),
		IntrinsicKindTwo::DivF32 =>
			*buf = (f32::from_bits(buf_to_u32(a)) / f32::from_bits(buf_to_u32(b))).to_bits() as u64,

		IntrinsicKindTwo::MulI   => *buf = buf_to_u64(a).wrapping_mul(buf_to_u64(b)),
		IntrinsicKindTwo::MulF64 =>
			*buf = (f64::from_bits(buf_to_u64(a)) * f64::from_bits(buf_to_u64(b))).to_bits(),
		IntrinsicKindTwo::MulF32 =>
			*buf = (f32::from_bits(buf_to_u32(a)) * f32::from_bits(buf_to_u32(b))).to_bits() as u64,

		IntrinsicKindTwo::Equal      => *buf = (buf_to_u64(a) == buf_to_u64(b)) as u64,
		IntrinsicKindTwo::NotEqual   => *buf = (buf_to_u64(a) != buf_to_u64(b)) as u64,
		IntrinsicKindTwo::Less       => *buf = (buf_to_u64(a) <  buf_to_u64(b)) as u64,
		IntrinsicKindTwo::LessEqu    => *buf = (buf_to_u64(a) <= buf_to_u64(b)) as u64,
		IntrinsicKindTwo::Greater    => *buf = (buf_to_u64(a) >  buf_to_u64(b)) as u64,
		IntrinsicKindTwo::GreaterEqu => *buf = (buf_to_u64(a) >= buf_to_u64(b)) as u64,

		IntrinsicKindTwo::BitAnd => *buf = buf_to_u64(a) & buf_to_u64(b),
		IntrinsicKindTwo::BitOr  => *buf = buf_to_u64(a) | buf_to_u64(b),
		IntrinsicKindTwo::BitXor => *buf = buf_to_u64(a) ^ buf_to_u64(b),

		IntrinsicKindTwo::PointerAdd { size } => *buf = buf_to_u64(a).wrapping_add(buf_to_u64(b) * size),
		IntrinsicKindTwo::PointerSub { size } => *buf = buf_to_u64(a).wrapping_sub(buf_to_u64(b) * size),
		IntrinsicKindTwo::PointerDiff { size } => *buf = buf_to_u64(a).wrapping_sub(buf_to_u64(b)) / size,
	};
}

fn buf_to_u64(buf: &[u8]) -> u64 {
	let mut to = [0u8; 8];

	let len = buf.len();
	to[.. len].copy_from_slice(buf);

	u64::from_le_bytes(to)
}

fn buf_to_u32(buf: &[u8]) -> u32 {
	let mut to = [0u8; 4];

	let len = buf.len();
	to[.. len].copy_from_slice(buf);

	u32::from_le_bytes(to)
}
