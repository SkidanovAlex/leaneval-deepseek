/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Jker` has total mass one

The rescaled kernel `Jker ρ ε p = ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)` of
`Submission/Work/FTS/StrongEps/Basic.lean` is the dilation of the admissible mollifier `ρ`
(`IsMollKernel ρ`: continuous, supported in the closed unit ball, nonnegative, total mass `1`)
by the factor `ε` in the two-dimensional log-coordinates `(s, ζ) = (log z, log tan θ)`.
Substituting `p = ε • q` (so that `dq = ε⁻² dp`) preserves the total mass:

  `∫ p, Jker ρ ε p = ∫ q, ρ q = 1`.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- **The change of variables `p ↦ ε⁻¹ • p` in `ℝ²`**, in the form used for `Jker`: the
Lebesgue integral of `p ↦ ρ (ε⁻¹ • p)` is `ε ^ 2` times the integral of `ρ` (`finrank ℝ (ℝ×ℝ) = 2`). -/
theorem integral_comp_inv_smul_two (ρ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, ρ (ε⁻¹ • p) = ε ^ 2 * ∫ p : ℝ × ℝ, ρ p := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := MeasureTheory.volume) (R := ε) (f := ρ) hε.le
  rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod], smul_eq_mul] at h
  exact h

/-- **The kernel `Jker ρ ε` has total mass one** for every admissible mollifier `ρ` and every
`ε > 0`. -/
theorem Jker_integral_eq_one (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := by
  have h1 : ∫ p : ℝ × ℝ, Jker ρ ε p = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, ρ (ε⁻¹ • p) := by
    simp only [Jker]
    rw [MeasureTheory.integral_const_mul]
  rw [h1, integral_comp_inv_smul_two ρ hε, hρ.mass, mul_one, ← mul_pow,
    inv_mul_cancel₀ hε.ne', one_pow]

end Work.FTS.StrongEps
