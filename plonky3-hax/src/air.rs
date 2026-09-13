//! Algebraic intermediate representations (AIRs) for the reference STARK.
//!
//! An AIR describes a computation as a matrix of field elements (the
//! execution trace) together with polynomial constraints that must hold on
//! every pair of consecutive rows and at given boundary positions.
//!
//! This module provides a row-major trace type, transition and boundary
//! constraints, and a checker for both. A transition constraint is selected
//! by a numeric tag (`kind`) that `eval_transition` dispatches on; the only
//! AIR defined is the two-column Fibonacci AIR.

use crate::specs::baby_bear::*;

/// A row-major trace matrix of Baby Bear field elements.
///
/// `cells[row * width + col]` is the field element at row `row`, column `col`.
pub struct Trace {
    pub width: usize,
    pub height: usize,
    pub cells: Vec<u64>,
}

impl Trace {
    /// Create a new trace with the given dimensions, filled with zeros.
    pub fn zeros(width: usize, height: usize) -> Self {
        Trace {
            width,
            height,
            cells: vec![0u64; width * height],
        }
    }

    /// Construct a trace from a row-major vector.
    pub fn from_cells(width: usize, height: usize, cells: Vec<u64>) -> Self {
        assert_eq!(cells.len(), width * height);
        Trace {
            width,
            height,
            cells,
        }
    }

    /// Read the value at (row, col).
    pub fn get(&self, row: usize, col: usize) -> u64 {
        self.cells[row * self.width + col]
    }

    /// Write the value at (row, col).
    pub fn set(&mut self, row: usize, col: usize, val: u64) {
        self.cells[row * self.width + col] = val;
    }

    /// Borrow a row as a slice.
    pub fn row(&self, row: usize) -> &[u64] {
        &self.cells[row * self.width..(row + 1) * self.width]
    }
}

// Transition-constraint tags. They are `usize` constants rather than an
// `enum`, so that the extracted model dispatches on a primitive numeric type.
// A new constraint is a new constant and a new branch in `eval_transition`.

/// Fibonacci AIR's first constraint: `next[0] − cur[1]`.
pub const FIB_NEXT_A: usize = 0;
/// Fibonacci AIR's second constraint: `next[1] − (cur[0] + cur[1])`.
pub const FIB_NEXT_B: usize = 1;

/// Evaluate a transition constraint on two consecutive rows.
pub fn eval_transition(kind: usize, cur: &[u64], next: &[u64]) -> u64 {
    if kind == FIB_NEXT_A {
        bb_sub(next[0], cur[1])
    } else {
        // FIB_NEXT_B (and any future kind defaults here — extend with
        // an `else if` per new constraint).
        bb_sub(next[1], bb_add(cur[0], cur[1]))
    }
}

/// A transition constraint: a predicate on two consecutive rows.
///
/// The constraint holds at step `i` iff
///   `eval_transition(kind, trace.row(i), trace.row(i + 1)) == 0`.
pub struct TransitionConstraint {
    pub name: &'static str,
    pub kind: usize,
    /// Upper bound on the polynomial degree of the constraint.
    pub degree: usize,
}

/// A boundary constraint: a claimed value at a specific (row, column).
pub struct BoundaryConstraint {
    pub row: usize,
    pub col: usize,
    pub value: u64,
}

/// Full AIR specification.
pub struct AirSpec {
    pub num_columns: usize,
    pub transitions: Vec<TransitionConstraint>,
    pub boundaries: Vec<BoundaryConstraint>,
}

/// Check all transition constraints on a trace.
///
/// Each transition constraint must evaluate to zero on every pair of
/// consecutive rows (there are `trace.height - 1` such pairs).
pub fn check_transitions(air: &AirSpec, trace: &Trace) -> bool {
    if trace.width != air.num_columns {
        return false;
    }
    if trace.height < 2 {
        // No transitions to check — vacuously true.
        return true;
    }

    // Accumulate a "valid so far" flag instead of returning early from
    // the inner loop. The Lean translation drops an inner `for` loop whose
    // body's only effect is an `early return`; accumulating keeps the
    // loop visible to the extraction.
    let mut ok = true;
    for i in 0..(trace.height - 1) {
        let row_i = trace.row(i);
        let row_next = trace.row(i + 1);
        for k in 0..air.transitions.len() {
            let c = &air.transitions[k];
            let v = eval_transition(c.kind, row_i, row_next);
            if v != 0 {
                ok = false;
            }
        }
    }

    ok
}

/// Check all boundary constraints on a trace.
pub fn check_boundaries(air: &AirSpec, trace: &Trace) -> bool {
    // Same accumulator pattern as `check_transitions`: avoid an early
    // return inside the loop, so that the Lean translation keeps the loop body.
    let mut ok = true;
    for i in 0..air.boundaries.len() {
        let b = &air.boundaries[i];
        if b.row >= trace.height || b.col >= trace.width {
            ok = false;
        } else if trace.get(b.row, b.col) != b.value {
            ok = false;
        }
    }
    ok
}

/// Full trace-validity check: transitions and boundaries.
pub fn trace_valid(air: &AirSpec, trace: &Trace) -> bool {
    check_transitions(air, trace) && check_boundaries(air, trace)
}

// -------------------------------------------------------------------------
// Example AIR: Fibonacci
//
// Columns: [a, b]. Transition: next.a = cur.b, next.b = cur.a + cur.b.
// Boundary: trace[0] = [0, 1].
// -------------------------------------------------------------------------

/// Width of the Fibonacci AIR trace (two columns: a and b).
pub const FIB_WIDTH: usize = 2;

/// Build the Fibonacci AIR specification.
///
/// Boundaries set `trace[0] = [0, 1]`, so successive rows contain
/// consecutive Fibonacci numbers (mod p).
pub fn fib_air() -> AirSpec {
    AirSpec {
        num_columns: FIB_WIDTH,
        transitions: vec![
            TransitionConstraint {
                name: "next.a = cur.b",
                kind: FIB_NEXT_A,
                degree: 1,
            },
            TransitionConstraint {
                name: "next.b = cur.a + cur.b",
                kind: FIB_NEXT_B,
                degree: 1,
            },
        ],
        boundaries: vec![
            BoundaryConstraint {
                row: 0,
                col: 0,
                value: 0,
            },
            BoundaryConstraint {
                row: 0,
                col: 1,
                value: 1,
            },
        ],
    }
}

/// Generate a valid Fibonacci trace of `height` rows.
pub fn fib_trace(height: usize) -> Trace {
    let mut t = Trace::zeros(FIB_WIDTH, height);
    if height == 0 {
        return t;
    }
    t.set(0, 0, 0);
    t.set(0, 1, 1);
    for i in 1..height {
        let a = t.get(i - 1, 0);
        let b = t.get(i - 1, 1);
        t.set(i, 0, b);
        t.set(i, 1, bb_add(a, b));
    }
    t
}

/// Maximum degree of all transition constraints in an AIR.
pub fn air_max_degree(air: &AirSpec) -> usize {
    let mut d: usize = 0;
    for i in 0..air.transitions.len() {
        if air.transitions[i].degree > d {
            d = air.transitions[i].degree;
        }
    }
    d
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fib_trace_valid() {
        let air = fib_air();
        let trace = fib_trace(16);
        assert!(trace_valid(&air, &trace));
    }

    #[test]
    fn test_fib_trace_values() {
        let trace = fib_trace(10);
        // First ten Fibonacci numbers: 0, 1, 1, 2, 3, 5, 8, 13, 21, 34
        let expected_b = [1u64, 1, 2, 3, 5, 8, 13, 21, 34, 55];
        for i in 0..10 {
            assert_eq!(trace.get(i, 1), expected_b[i], "row {}", i);
        }
    }

    #[test]
    fn test_fib_trace_tampered_transition_fails() {
        let air = fib_air();
        let mut trace = fib_trace(16);
        // Corrupt row 5
        trace.set(5, 1, bb_add(trace.get(5, 1), 1));
        assert!(!trace_valid(&air, &trace));
    }

    #[test]
    fn test_fib_trace_tampered_boundary_fails() {
        let air = fib_air();
        let mut trace = fib_trace(16);
        // Corrupt the boundary
        trace.set(0, 0, 7);
        assert!(!trace_valid(&air, &trace));
    }

    #[test]
    fn test_wrong_width_rejected() {
        let air = fib_air();
        let bad = Trace::zeros(3, 16);
        assert!(!trace_valid(&air, &bad));
    }

    #[test]
    fn test_air_max_degree() {
        let air = fib_air();
        assert_eq!(air_max_degree(&air), 1);
    }
}
