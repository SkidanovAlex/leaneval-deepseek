import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Work

open scoped Real
open Work.FTS.StrongEps
open MeasureTheory

/-- `Jeps` is `ℝ`-homogeneous in the profile: `J_ε(c f) = c · J_ε f`.

This is immediate from the definition: on the open quadrant `Jeps` is the log-coordinate
convolution `p ↦ Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)`, and on the boundary both sides
vanish; the only ingredient is the linearity of the Bochner integral in the scalar factor. -/
theorem Jeps_smul (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (f : Work.FTS.Galerkin.Fn) :
    Work.FTS.StrongEps.Jeps ρ ε (c • f) = c • Work.FTS.StrongEps.Jeps ρ ε f := by
  funext z θ
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Jeps_eq_integral ρ ε (c • f) hc.1 hc.2, Jeps_eq_integral ρ ε f hc.1 hc.2]
    rw [← integral_const_mul c (fun p : ℝ × ℝ =>
      Jker ρ ε p * f (zShift z p.1) (thShift θ p.2))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring)
  · rw [Jeps_eq_zero ρ ε (c • f) hc, Jeps_eq_zero ρ ε f hc, mul_zero]

end Work.FTS.StrongEps.EpsE4Work
