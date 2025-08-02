#[allow(non_upper_case_globals)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(dead_code)]
#[allow(clippy::useless_transmute)]
#[allow(clippy::ptr_offset_with_cast)]
pub(super) mod lean
{
	include!(concat!(env!("OUT_DIR"), "/lean.rs"));
}

pub type World = *const ();
pub type IOResult = lean::lean_obj_res;

/// Create the world dummy required in IO Monads. Does not allocate
#[allow(unused)]
pub fn world() -> IOResult
{
	unsafe { lean::lean_io_mk_world() }
}
pub fn unit() -> lean::lean_obj_res
{
	unsafe { lean::lean_box(0) }
}
