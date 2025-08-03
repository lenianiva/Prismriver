use crate::primitive;

use std::{error::Error, thread::sleep, time::Duration};

use midir;

fn play_note(conn: &mut midir::MidiOutputConnection, note: u8, duration: u64)
{
	const NOTE_ON_MSG: u8 = 0x90;
	const NOTE_OFF_MSG: u8 = 0x80;
	const VELOCITY: u8 = 0x64;
	// We're ignoring errors in here
	let _ = conn.send(&[NOTE_ON_MSG, note, VELOCITY]);
	sleep(Duration::from_millis(duration * 150));
	let _ = conn.send(&[NOTE_OFF_MSG, note, VELOCITY]);
}

pub fn connect_play_note(note: u8) -> Result<(), Box<dyn Error>>
{
	use std::io::Write;

	eprintln!("Playing midi note {}", note);
	std::io::stderr().flush()?;
	let midi_output = midir::MidiOutput::new("prismriver")?;
	let out_ports = midi_output.ports();
	let out_port = out_ports.get(1).ok_or("No MIDI output ports available")?;
	eprintln!("Using port {}", out_port.id());
	let mut conn = midi_output.connect(out_port, "play")?;
	play_note(&mut conn, note, 1);
	Ok(())
}

#[no_mangle]
pub extern "C" fn prismriver_mystery(x: u8) -> u8
{
	255 - x
}
#[no_mangle]
pub extern "C" fn prismriver_ping(x: u8, _: primitive::lean::lean_obj_arg) -> primitive::IOResult
{
	if let Err(e) = connect_play_note(x) {
		eprintln!("Error occurred: {e}");
	}
	primitive::io_unit()
}

