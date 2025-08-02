#[no_mangle]
pub extern "C" fn prismriver_ping(x: i32) -> i32 {
	return x * 2;
}
