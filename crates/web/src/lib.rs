//! WebAssembly bindings: a reduction the page can step through.
//!
//! The page hands over a script, asks for steps, and draws the frames it gets
//! back as JSON. All the logic lives in [`stepper`] and in `layout`, which
//! places the nets on the page. Both are plain Rust and are tested as such.

mod layout;
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
        self.run(1, false)
    }

    /// Fires up to `interactions` interactions in one go, stopping after the
    /// first beta among them if `until_beta`. Returns the name of the rule
    /// fired last, or nothing if the net was in normal form already.
    pub fn run(&mut self, interactions: u32, until_beta: bool) -> Result<Option<String>, JsError> {
        let fired = self
            .stepper
            .advance(u64::from(interactions), until_beta)
            .map_err(|halt| JsError::new(&halt.to_string()))?;
        Ok(fired.map(|rule| rule_name(rule).to_owned()))
    }

    /// Interactions fired so far.
    pub fn steps(&self) -> f64 {
        // Exact up to 2^53, which no reduction on a page gets near.
        self.stepper.steps() as f64
    }

    /// Undoes the last interaction. Returns whether there was one to undo.
    pub fn back(&mut self) -> bool {
        self.stepper.back()
    }

    /// Goes back to the term as it was loaded.
    pub fn reset(&mut self) {
        self.stepper.reset();
    }

    /// The current frame, as JSON. The picture of the net is left out if it
    /// has more than `max_nodes` nodes.
    pub fn frame(&self, max_nodes: u32) -> Result<String, JsError> {
        let max_nodes = usize::try_from(max_nodes).unwrap_or(usize::MAX);
        serde_json::to_string(&self.stepper.frame(max_nodes))
            .map_err(|error| JsError::new(&error.to_string()))
    }
}
