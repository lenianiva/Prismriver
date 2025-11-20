use std::{ffi::CStr, marker::PhantomData};

#[allow(non_upper_case_globals)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(dead_code)]
#[allow(clippy::useless_transmute)]
#[allow(clippy::ptr_offset_with_cast)]
pub(super) mod lean {
	include!(concat!(env!("OUT_DIR"), "/lean.rs"));

	#[link(name = "leanshared")]
	#[link(name = "Init_shared")]
	extern "C" {
		#[link_name = "lean_initialize_runtime_module"]
		pub fn initialize_runtime_module();
		#[link_name = "lean_initialize"]
		pub fn initialize();
	}
	#[link(name = "leanextern", kind = "static")]
	extern "C" {
		#[link_name = "lean_dec__leanextern"]
		pub fn dec(obj: lean_obj_arg);
	}
}

pub type IOResult = lean::lean_obj_res;

/// Create the world dummy required in IO Monads. Does not allocate
#[allow(unused)]
pub fn world() -> lean::lean_obj_res {
	unsafe { lean::lean_io_mk_world() }
}
#[allow(unused)]
pub fn unit() -> lean::lean_obj_res {
	unsafe { lean::lean_box(0) }
}
pub fn io_unit() -> IOResult {
	unsafe { lean::lean_io_result_mk_ok(lean::lean_box(0)) }
}

pub trait LeanPtr: Clone {
	fn to_pointer(&self) -> lean::b_lean_obj_arg;
	fn to_arg(self) -> lean::lean_obj_arg;
	/// Caller must ensure this is a `nat`
	unsafe fn nat_to_usize(&self) -> usize {
		unsafe { lean::lean_usize_of_nat(self.to_pointer()) }
	}
	fn tag(&self) -> u32 {
		unsafe { lean::lean_obj_tag(self.to_pointer()) }
	}
	// ctor functions
	fn is_ctor(&self) -> bool {
		unsafe { lean::lean_is_ctor(self.to_pointer()) }
	}
	unsafe fn n_objects(&self) -> u32 {
		unsafe { lean::lean_ctor_num_objs(self.to_pointer()) }
	}
}
#[repr(transparent)]
pub struct LeanObj {
	p: *mut lean::lean_object,
}
impl LeanObj {
	/// Take ownership of a lean object
	unsafe fn new(p: lean::lean_obj_arg) -> Self {
		assert!(!p.is_null());
		Self { p }
	}
	/// Acquire a borrowed lean object
	unsafe fn upgrade(p: lean::b_lean_obj_arg) -> Self {
		assert!(!p.is_null());
		unsafe { lean::lean_inc(p) };
		Self { p }
	}
	fn borrow(&self) -> lean::b_lean_obj_res {
		self.p
	}
	pub fn as_ref(&self) -> LeanRef<'_> {
		LeanRef::from(self)
	}
}
impl Drop for LeanObj {
	fn drop(&mut self) {
		if !self.p.is_null() {
			unsafe { lean::dec(self.p) };
		}
	}
}
impl Clone for LeanObj {
	fn clone(&self) -> Self {
		unsafe { Self::upgrade(self.borrow()) }
	}
}
impl LeanPtr for LeanObj {
	fn to_pointer(&self) -> lean::b_lean_obj_arg {
		self.p
	}
	/// Consumes this object and turn it into a raw unmanaged pointer. This
	/// effectively passes the virtual RC token to the caller.
	fn to_arg(mut self) -> lean::lean_obj_arg {
		let result = self.p;
		// prevent dropping
		self.p = std::ptr::null_mut();
		result
	}
}
impl<'o> From<&'o LeanObj> for LeanRef<'o> {
	fn from(o: &'o LeanObj) -> Self {
		Self {
			p: o.p,
			parent: std::marker::PhantomData,
		}
	}
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct LeanRef<'o> {
	p: *mut lean::lean_object,
	parent: PhantomData<&'o LeanObj>,
}
impl<'o> LeanRef<'o> {
	unsafe fn new(p: lean::b_lean_obj_res) -> Self {
		assert!(!p.is_null());
		Self {
			p,
			parent: PhantomData,
		}
	}
	pub fn unbox(&self) -> usize {
		debug_assert!(unsafe { lean::lean_is_scalar(self.p) });
		unsafe { lean::lean_unbox(self.p) }
	}
	pub fn to_bool(self) -> bool {
		self.unbox() != 0
	}
	pub fn upgrade(&self) -> LeanObj {
		unsafe { LeanObj::upgrade(self.p) }
	}
	unsafe fn unwrap_io_result(&self) -> Self {
		debug_assert_eq!(
			unsafe { lean::lean_ctor_num_objs(self.p) },
			2,
			"IO result must have 2 objects (the second field is a dummy)"
		);
		if self.tag() != 0 {
			eprintln!("Trying to unwrap IO error!");
		}
		if unsafe { lean::lean_io_result_is_error(self.p) } {
			unsafe { lean::lean_io_result_show_error(self.p) };
			panic!("IO error!");
		}
		debug_assert!(unsafe { lean::lean_io_result_is_ok(self.p) });
		unsafe { LeanRef::new(lean::lean_io_result_get_value(self.p)) }
	}
	pub fn to_str(self) -> &'o str {
		debug_assert!(!self.p.is_null());
		debug_assert!(unsafe { lean::lean_is_string(self.p) });
		unsafe { CStr::from_ptr(lean::lean_string_cstr(self.p)) }
			.to_str()
			.expect("Invalid C-string")
	}
	/// Iterates through a Lean array
	pub fn array_iter(&self) -> impl ExactSizeIterator<Item = LeanRef<'o>> {
		assert!(
			unsafe { lean::lean_is_array(self.p) },
			"iter_array can only be called on arrays, but the object tag is {}",
			unsafe { lean::lean_ptr_tag(self.p) },
		);
		let size = unsafe { lean::lean_array_size(self.p) };
		let cptr = unsafe { lean::lean_array_cptr(self.p) };
		(0..size).map(move |i| Self {
			p: unsafe { *cptr.add(i) },
			parent: PhantomData,
		})
	}
}
impl LeanPtr for LeanRef<'_> {
	fn to_pointer(&self) -> lean::b_lean_obj_arg {
		self.p
	}
	fn to_arg(self) -> lean::lean_obj_arg {
		let p = self.p;
		debug_assert!(!p.is_null());
		unsafe { lean::lean_inc(p) };
		p
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn test_placeholder() {
		assert_eq!(0, 0);
	}
}
