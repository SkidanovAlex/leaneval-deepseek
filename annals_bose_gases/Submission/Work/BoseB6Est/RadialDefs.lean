import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6Est.Regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the radial data of the `I₁` estimate

This small module only fixes the two radial integrands used by the `I₁`
estimate `fsI1_le`:

* `fsGR K εT c1 c2 r = (τ̃(r)+β(r)) − √((τ̃(r)+β(r))²−β(r)²) − β(r)²/(2r²)`,
  the radial form of `fsI1Integrand` (its `τ̃` is FS's `fsTau`);
* `fsG0R r = lhyRad (8π) r`, the model integrand `(r²+8π) − √((r²+8π)²−(8π)²) − (8π)²/(2r²)`.

Everything else about them is proved in the sibling modules.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

local notation "ℝ³" => Fin 3 → ℝ

/-- The radial version of the `I₁` integrand `α − √(α²−β²) − β²/(2r²)` with
`α = τ̃(r) + β(r)`. -/
def fsGR (K : FsKernel) (εT c1 c2 r : ℝ) : ℝ :=
  (Work.BoseB6.fsTau εT c1 c2 r + K.β r)
    - Real.sqrt ((Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2)
    - (K.β r) ^ 2 / (2 * r ^ 2)

/-- The model radial integrand `lhyRad (8π)`, i.e. the `β = 8π`, `τ̃ = r²` case. -/
def fsG0R (r : ℝ) : ℝ :=
  (r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2 + 8 * Real.pi) ^ 2 - (8 * Real.pi) ^ 2)
    - (8 * Real.pi) ^ 2 / (2 * r ^ 2)

theorem fsG0R_eq_lhyRad (r : ℝ) : fsG0R r = Work.BoseB6.lhyRad (8 * Real.pi) r := rfl

theorem lhyR3_eq_fsG0R (x : ℝ³) :
    Work.BoseB6.lhyR3 (8 * Real.pi) x = fsG0R (nrm x) := rfl

end Work.BoseB6Est
