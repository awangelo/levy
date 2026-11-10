//! WebAssembly bindings: a reduction the page can step through.
//!
//! The page hands over a script, asks for steps, and draws the frames it gets
//! back as JSON. All the logic lives in [`stepper`], which is plain Rust and
//! is tested as such.

pub mod stepper;

use wasm_bindgen::prelude::*;

use stepper::{Stepper, rule_name};

/// A reduction in progress.
#[wasm_bindgen]
pub struct Session {
    stepper: Stepper,
}

#[wasm_bindgen]
impl Session {
    /// Loads a script: definitions followed by the term to reduce.
    #[wasm_bindgen(constructor)]
    pub fn new(script: &str) -> Result<Session, JsError> {
        let stepper = Stepper::load(script).map_err(|message| JsError::new(&message))?;
        Ok(Session { stepper })
    }

    /// Fires one interaction. Returns the name of its rule, or nothing if
    /// the net is in normal form.
    pub fn step(&mut self) -> Result<Option<String>, JsError> {
        let fired = self
            .stepper
            .step()
            .map_err(|halt| JsError::new(&halt.to_string()))?;
        Ok(fired.map(|rule| rule_name(rule).to_owned()))
    }

    /// Undoes the last step. Returns whether there was one to undo.
    pub fn back(&mut self) -> bool {
        self.stepper.back()
    }

    /// Goes back to the term as it was loaded.
    pub fn reset(&mut self) {
        self.stepper.reset();
    }

    /// The current frame, as JSON.
    pub fn frame(&self) -> Result<String, JsError> {
        serde_json::to_string(&self.stepper.frame())
            .map_err(|error| JsError::new(&error.to_string()))
    }
}
