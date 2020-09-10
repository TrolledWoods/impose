pub trait Id {
	fn new() -> Self;
	fn create(value: u32) -> Self;
	fn get(&self) -> u32;
	fn count_next(&mut self) -> Self;
}

macro_rules! create_id {
	($name:ident) => {
		/// Ids start at 0 and keep going up. This is useful because you can have a Vec
		/// of items, and use Ids to keep track of them.
		#[derive(Clone, Copy, PartialEq, Eq, Hash)]
		pub struct $name(std::num::NonZeroU32);

		impl $name {
			#[allow(unused)]
			pub fn into_index(self) -> usize {
				(self.0.get() - 1) as usize
			}
		}

		impl crate::id::Id for $name {
			#[allow(unused)]
			fn new() -> Self {
				Self(std::num::NonZeroU32::new(1).unwrap())
			}

			#[allow(unused)]
			fn get(&self) -> u32 {
				self.0.get() - 1
			}

			#[allow(unused)]
			fn create(value: u32) -> Self {
				Self(std::num::NonZeroU32::new(value + 1).unwrap())
			}

			#[allow(unused)]
			fn count_next(&mut self) -> Self {
				let value = *self;
				self.0 = std::num::NonZeroU32::new(self.0.get() + 1).unwrap();
				value
			}
		}

		impl std::fmt::Debug for $name {
			fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
				write!(f, stringify!($name))?;
				write!(f, "({})", self.0)?;
				Ok(())
			}
		}

		impl std::fmt::Display for $name {
			fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
				write!(f, "{}", self.0)
			}
		}
	}
}

#[derive(Debug)]
pub struct IdVec<T, I> where I: Id {
	contents: Vec<T>,
	_phantom: std::marker::PhantomData<I>,
}

impl<T, I> Default for IdVec<T, I> where I: Id {
	fn default() -> Self {
		Self {
			contents: Vec::new(),
			_phantom: std::marker::PhantomData,
		}
	}
}

impl<T, I> IdVec<T, I> where I: Id {
	pub fn new() -> Self {
		Self { 
			contents: Vec::new(),
			_phantom: std::marker::PhantomData,
		}
	}

	pub fn iter_ids(&self) -> impl Iterator<Item = (I, &T)> {
		self.contents.iter().enumerate().map(|(i, v)| (I::create(i as u32), v))
	}

	pub fn get(&self, index: I) -> &T {
		&self.contents[index.get() as usize]
	}

	pub fn get_mut(&mut self, index: I) -> &mut T {
		&mut self.contents[index.get() as usize]
	}

	pub fn push(&mut self, item: T) -> I {
		let id = self.contents.len() as u32;
		self.contents.push(item);
		I::create(id)
	}
}

impl<T, I> std::ops::Deref for IdVec<T, I> where I: Id {
	type Target = [T];

	fn deref(&self) -> &Self::Target {
		&*self.contents
	}
}

impl<T, I> std::ops::DerefMut for IdVec<T, I> where I: Id {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut *self.contents
	}
}
