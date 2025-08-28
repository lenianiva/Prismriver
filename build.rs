use std::{env, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>>
{
	let lean_root = env::var("LEAN_ROOT").expect("$LEAN_ROOT must exist");
	let output_path = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR must be present"));
	let input = format!("{lean_root}/include/lean/lean.h");

	println!("cargo:rustc-link-search={lean_root}/lib/lean");

	// Generate headers

	let bindgen_dir = env::temp_dir().join("bindgen");
	let extern_src_path = bindgen_dir.join("leanextern.c");

	let bindings = bindgen::Builder::default()
		.header(&input)
		// Tell cargo to invalidate the built crate whenever any of the
		// included header files changed.
		.parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
		// The following is specific to `lean.h`: There are a lot of static
		// function
		.wrap_static_fns(true)
		.wrap_static_fns_suffix("__leanextern")
		.wrap_static_fns_path(&extern_src_path)
		// but some functions use `_Atomic(int)` types that bindgen cannot handle,
		// so they are blocklisted. The types which use `_Atomic` are treated as
		// opaque.
		.blocklist_function("lean_get_rc_mt_addr")
		.opaque_type("lean_thunk_object")
		.opaque_type("lean_task_object")
		.clang_arg(format!("-I{lean_root}/include"))
		.generate()?;

	bindings.write_to_file(output_path.join("lean.rs"))?;

	let extern_obj_path = bindgen_dir.join("leanextern.o");

	// Compile the generated wrappers into an object file.
	let clang_output = std::process::Command::new("clang")
		.arg("-O")
		.arg("-c")
		.arg("-o")
		.arg(&extern_obj_path)
		.arg(&extern_src_path)
		.arg("-include")
		.arg(&input)
		.arg(format!("-I{lean_root}/include"))
		.output()?;
	if !clang_output.status.success() {
		panic!(
			"Could not compile object file:\n{}",
			String::from_utf8_lossy(&clang_output.stderr)
		);
	}

	// Turn the object file into a static library
	#[cfg(not(target_os = "windows"))]
	let lib_output = std::process::Command::new("ar")
		.arg("rcs")
		.arg(bindgen_dir.join("libleanextern.a"))
		.arg(&extern_obj_path)
		.output()?;
	#[cfg(target_os = "windows")]
	let lib_output = std::process::Command::new("LIB")
		.arg(&extern_obj_path)
		.arg(format!(
			"/OUT:{}",
			bindgen_dir.join("libleanextern.lib").display()
		))
		.output()?;
	if !lib_output.status.success() {
		panic!(
			"Could not emit library file:\n{}",
			String::from_utf8_lossy(&lib_output.stderr)
		);
	}

	// Statically link against the generated lib
	println!("cargo:rustc-link-search={}", bindgen_dir.display());
	println!("cargo:rustc-link-lib=static=leanextern");

	Ok(())
}
