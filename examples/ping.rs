use std::{
	error::Error,
	io::{stdin, stdout, Write},
	thread::sleep,
	time::Duration,
};

use midir::{MidiOutput, MidiOutputPort};

use prismriver::midi;

fn main() -> Result<(), Box<dyn std::error::Error>>
{
	midi::connect_play_note(64)?;
	Ok(())
}
