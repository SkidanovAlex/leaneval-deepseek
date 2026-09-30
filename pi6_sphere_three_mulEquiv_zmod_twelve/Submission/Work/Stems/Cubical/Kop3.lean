import Mathlib
import Submission.Work.Stems.Cubical.Kop2

/-!
# The `K`-operator on `1`-cubes, constructed explicitly

We build the square `K₁(s)` for a `1`-cube `s` explicitly, as a "cone" on its boundary loop.  The
boundary loop is spliced (counterclockwise from `(0,0)`) as
`K₀(s(0)) · s · K₀(s(1))⁻¹ · const(x₀)`, and a null-homotopy of this loop (simple connectivity of
`X`) provides the filling via a radial parametrisation of the square.
-/

open scoped unitInterval Topology

namespace Work.Stems.Cubical

variable {X : Type} [TopologicalSpace X]

/-- The boundary loop of the `K₁`-square, with its four segments. -/
noncomputable def K1loop2 (x₀ : X) [PathConnectedSpace X] (s : CubeCM 1 X) : Path x₀ x₀ :=
  (((K0 x₀ (s (icOnePt 0))).trans (cubeToOnePath s)).trans
    (K0 x₀ (s (icOnePt 1))).symm).trans (Path.refl x₀)

/-- Chebyshev radius: `1` on the boundary of `I^2`, `0` at its centre. -/
def cheb (t : IC 2) : ℝ :=
  max |2 * (t 0 : ℝ) - 1| |2 * (t 1 : ℝ) - 1|

theorem cheb_nonneg (t : IC 2) : 0 ≤ cheb t := le_max_of_le_left (abs_nonneg _)

theorem cheb_le_one (t : IC 2) : cheb t ≤ 1 := by
  have h0 : (t 0 : ℝ) ≤ 1 := t 0 |>.2.2
  have h0' : 0 ≤ (t 0 : ℝ) := (t 0).2.1
  have h1 : (t 1 : ℝ) ≤ 1 := (t 1).2.2
  have h1' : 0 ≤ (t 1 : ℝ) := (t 1).2.1
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith

/-- The boundary position (piecewise-linear on the four triangles of `I^2`). -/
noncomputable def bpos (t : IC 2) : ℝ :=
  let a : ℝ := t 0
  let b : ℝ := t 1
  if b ≤ a ∧ b ≤ 1 - a then (a - b) / 4
  else if a ≥ b ∧ a ≥ 1 - b then -1 / 2 + 3 * a / 4 + b / 4
  else if b ≥ a ∧ b ≥ 1 - a then -1 / 4 + a / 4 + 3 * b / 4
  else a / 4 - b / 4 + 3 / 4

end Work.Stems.Cubical
