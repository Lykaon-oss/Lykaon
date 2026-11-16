//! lykaon-core: the typed tree, the value model and the interpreter.
//! Shared by the compiler (`lykaon`) and the runtime library (`lykaon-rt`)
//! that is linked into every built program.

pub mod args;
pub mod formats;
pub mod interp;
pub mod mir;
pub mod net;
pub mod sem;
pub mod signals;
pub mod time4;
