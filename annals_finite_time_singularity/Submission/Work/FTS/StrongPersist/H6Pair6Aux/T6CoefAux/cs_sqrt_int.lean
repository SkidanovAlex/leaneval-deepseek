import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open MeasureTheory

/-- Cauchy–Schwarz for square roots of nonnegative integrable functions. -/
theorem cs_sqrt_int {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β} {A B : β → ℝ}
    (hA : MeasureTheory.Integrable A μ) (hB : MeasureTheory.Integrable B μ)
    (hAnn : 0 ≤ᵐ[μ] A) (hBnn : 0 ≤ᵐ[μ] B) :
    MeasureTheory.Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x)) μ ∧
      (∫ x, Real.sqrt (A x) * Real.sqrt (B x) ∂μ)
        ≤ Real.sqrt (∫ x, A x ∂μ) * Real.sqrt (∫ x, B x ∂μ) := by
  -- `√A` and `√B` are `L²` functions, so their product is `L¹` (Hölder with `p = q = 2`).
  have hsmA : AEStronglyMeasurable (fun x => Real.sqrt (A x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hsmB : AEStronglyMeasurable (fun x => Real.sqrt (B x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hsqA : (fun x => Real.sqrt (A x) ^ 2) =ᵐ[μ] A := by
    filter_upwards [hAnn] with x hx
    exact Real.sq_sqrt hx
  have hsqB : (fun x => Real.sqrt (B x) ^ 2) =ᵐ[μ] B := by
    filter_upwards [hBnn] with x hx
    exact Real.sq_sqrt hx
  -- the same statement for the real power `(·) ^ (2 : ℝ)`, used by the `Lp` machinery
  have hsqAr : (fun x => Real.sqrt (A x) ^ (2 : ℝ)) =ᵐ[μ] A := by
    filter_upwards [hsqA] with x hx
    rwa [Real.rpow_two]
  have hsqBr : (fun x => Real.sqrt (B x) ^ (2 : ℝ)) =ᵐ[μ] B := by
    filter_upwards [hsqB] with x hx
    rwa [Real.rpow_two]
  have hmemA : MemLp (fun x => Real.sqrt (A x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsmA).2 (hA.congr hsqA.symm)
  have hmemB : MemLp (fun x => Real.sqrt (B x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsmB).2 (hB.congr hsqB.symm)
  have hmemA' : MemLp (fun x => Real.sqrt (A x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hmemA
  have hmemB' : MemLp (fun x => Real.sqrt (B x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hmemB
  have hnnA : 0 ≤ᵐ[μ] fun x => Real.sqrt (A x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hnnB : 0 ≤ᵐ[μ] fun x => Real.sqrt (B x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hnnA hnnB hmemA' hmemB'
  have heqA : (∫ x, Real.sqrt (A x) ^ (2 : ℝ) ∂μ) = ∫ x, A x ∂μ := integral_congr_ae hsqAr
  have heqB : (∫ x, Real.sqrt (B x) ^ (2 : ℝ) ∂μ) = ∫ x, B x ∂μ := integral_congr_ae hsqBr
  have hInt : Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x)) μ :=
    (hmemA.integrable_mul hmemB).congr (Filter.Eventually.of_forall fun x => rfl)
  have hstep : (∫ x, Real.sqrt (A x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        * (∫ x, Real.sqrt (B x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      = Real.sqrt (∫ x, A x ∂μ) * Real.sqrt (∫ x, B x ∂μ) := by
    rw [heqA, heqB, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact ⟨hInt, hholder.trans_eq hstep⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
