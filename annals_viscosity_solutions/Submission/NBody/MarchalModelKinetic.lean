import Submission.NBody.MarchalTransferData
import Submission.NBody.MarchalStandardVariation
import Submission.NBody.MarchalCircleAvg

/-!
# Elementary facts for the model (kinetic) part of the variational argument

The model action difference of the standard variation splits into a kinetic and a potential part.
This module collects the elementary algebraic/calculus facts used by both:

* `deriv_blowUpProfile` — the derivative of the parabolic blow-up `q̄(t) = √κ t^{2/3} s̄`;
* `singleBodyVec_smul`, `stdPertVec_smul` — linearity of the standard-variation directions in the
  displacement vector (so that `δ = ρ • e_θ` gives displacements proportional to `ρ`);
* `stdCoef_smul_norm_one` — the coefficient of the standard variation of `ρ • e` is
  `min 1 (max 0 ((T-t)/ρ))` when `‖e‖ = 1`.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma singleBodyVec_smul (k : Fin N) (c : ℝ) (v : E) :
    singleBodyVec k (c • v) = c • singleBodyVec k v := by
  refine PiLp.ext fun i => ?_
  by_cases hi : i = k <;> simp [singleBodyVec, hi]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma singleBodyVec_add (k : Fin N) (v w : E) :
    singleBodyVec k (v + w) = singleBodyVec k v + singleBodyVec k w := by
  refine PiLp.ext fun i => ?_
  by_cases hi : i = k <;> simp [singleBodyVec, hi]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The standard-variation direction is linear in the displacement vector. -/
lemma stdPertVec_smul (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (c : ℝ) (v : E) :
    stdPertVec m k i₀ (c • v) = c • stdPertVec m k i₀ v := by
  rw [stdPertVec, stdPertVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [singleBodyVec_smul, smul_smul, mul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The coefficient of the standard variation of `ρ • e` for a unit vector `e`. -/
lemma stdCoef_smul_norm_one {ρ T t : ℝ} (hρ : 0 < ρ) {v : E} (hv : ‖v‖ = 1) :
    stdCoef (ρ • v) T t = min 1 (max 0 ((T - t) / ρ)) := by
  rw [stdCoef, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hv, mul_one]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the parabolic blow-up profile. -/
lemma deriv_blowUpProfile (κ : ℝ) (sbar : EN E N) {t : ℝ} (ht : 0 < t) :
    deriv (blowUpProfile κ sbar) t
      = ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ ((2:ℝ)/3))
      (((2:ℝ)/3) * t ^ ((2:ℝ)/3 - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))
  have h2 : HasDerivAt (fun x : ℝ => x ^ ((2:ℝ)/3) • (Real.sqrt κ • sbar))
      ((((2:ℝ)/3) * t ^ ((2:ℝ)/3 - 1)) • (Real.sqrt κ • sbar)) t :=
    h1.smul_const _
  have h3 : (fun x : ℝ => x ^ ((2:ℝ)/3) • (Real.sqrt κ • sbar)) = blowUpProfile κ sbar := by
    funext x
    rw [blowUpProfile, smul_smul, mul_comm]
  have h4 : (((2:ℝ)/3) * t ^ ((2:ℝ)/3 - 1)) • (Real.sqrt κ • sbar)
      = ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) • sbar := by
    rw [show ((2:ℝ)/3 - 1) = -(1:ℝ)/3 by norm_num]
    module
  rw [← h3, h2.deriv, h4]

end Submission.NBody
