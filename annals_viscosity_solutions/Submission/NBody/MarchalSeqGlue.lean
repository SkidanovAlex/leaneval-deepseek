import Submission.NBody.MarchalModelSplit
import Submission.NBody.MarchalBumpTransfer

/-!
# The transfer glue in the `stdVarVecDeriv` form

`modelDiff_eq_transfer_integrand` (`MarchalModelSplit`) expresses `modelDiff δ` as the integral of
the transfer integrand with `deriv (stdVarVec m k i₀ δ T)` in place of `f'`.  The sequential
transfer (`tendsto_transfer_of_data_seq`) is stated with an *everywhere bounded* `f'`, and the
almost-everywhere derivative `stdVarVecDeriv` is the only available candidate.  This file records
the (a.e.-congruent) version of the glue with `stdVarVecDeriv`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The transfer glue, derivative form.** -/
theorem modelDiff_eq_transfer_integrand_deriv {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (sbar : EN E N) {δ : E} (hδ : δ ≠ 0)
    (hint : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
      (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
        - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) volume 0 T) :
    modelDiff m k i₀ κ sbar T δ
      = ∫ s in (0:ℝ)..T, (massInner m (deriv (blowUpProfile κ sbar) s)
          (stdVarVecDeriv m k i₀ δ T s)
        + (1/2) * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2
        + clusterPotential m k (blowUpProfile κ sbar s + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (blowUpProfile κ sbar s)) := by
  rw [modelDiff_eq_transfer_integrand hm hi₀ hκ hT sbar hδ hint]
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hT]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp (by
    filter_upwards [deriv_stdVarVec_ae m k i₀ δ T hδ] with s hs
    rw [hs])

end Submission.NBody
