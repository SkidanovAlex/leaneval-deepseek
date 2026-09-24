import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_main

open MeasureTheory
open scoped ENNReal

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

/-- The CDF of the reference sum `Σ_{k ≥ 1} e^{-S_k}` for iid standard exponentials, on the
sharp range `θ ≤ 1`:
`P(Σ_{k ≥ 1} e^{-S_k} < θ) = θ / e^γ`. -/
theorem refsum_cdf {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (hEmeas : ∀ i, AEMeasurable (E i) P)
    (hElaw : ∀ i, Work.ChenPlan.LinearSieve.Selberg.Alt.IsStdExp (E i) P)
    (hindep : ProbabilityTheory.iIndepFun E P)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ENNReal.toReal (P (Work.ChenPlan.LinearSieve.Selberg.Alt.refSumLt E θ))
      = θ / Real.exp Real.eulerMascheroniConstant := by
  have hlaw := map_seq_eq_canonM P E hEmeas hElaw hindep
  have hameas : AEMeasurable (fun ω i => E i ω) P := aemeasurable_pi_iff.mpr hEmeas
  have hset : (fun ω => fun i => E i ω) ⁻¹' (cSet θ) = refSumLt E θ := by
    ext ω; rfl
  rw [← hset, ← Measure.map_apply_of_aemeasurable hameas (measurableSet_cSet θ), hlaw,
    cdf_canonM θ hθ0 hθ1, ENNReal.toReal_ofReal (by positivity), Real.exp_neg,
    div_eq_mul_inv]

end Work.ChenPlan.LinearSieve.Selberg.Alt
