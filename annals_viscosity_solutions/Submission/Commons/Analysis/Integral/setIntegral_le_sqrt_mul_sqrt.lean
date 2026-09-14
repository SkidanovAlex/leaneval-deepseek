import Mathlib.MeasureTheory.Function.L2Space

namespace Commons.Analysis.Integral

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Cauchy--Schwarz (Hölder with conjugate exponents `2, 2`) for set integrals of a nonnegative
measurable real function whose square is integrable on the set:
`∫ x in s, g x ≤ √(μ s) * √(∫ x in s, g x ^ 2)`. -/
theorem setIntegral_le_sqrt_mul_sqrt {α : Type*} [MeasureSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμ : μ s < ⊤) {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Measurable g) (hg2 : IntegrableOn (fun x ↦ g x ^ 2) s μ) :
    ∫ x in s, g x ∂μ ≤ Real.sqrt (μ s).toReal * Real.sqrt (∫ x in s, g x ^ 2 ∂μ) := by
  -- `g` lies in `L²(μ.restrict s)`: its square is integrable there and it is measurable.
  have hgmem : MemLp g 2 (μ.restrict s) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg2
  -- the constant `1` lies in `L²(μ.restrict s)` because `μ.restrict s` is a finite measure.
  have hmem1 : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal 2) (μ.restrict s) :=
    (memLp_const_iff (p := ENNReal.ofReal 2) (c := (1 : ℝ)) (by norm_num) (by norm_num)).mpr
      (Or.inr (by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact hμ))
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- Hölder's inequality with exponents `2, 2` on `μ.restrict s`, for `g` and the constant `1`.
  have hHold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict s) (p := 2) (q := 2)
    hpq (Eventually.of_forall hg0) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hgmem) hmem1
  -- identify the two sides with the quantities in the statement
  have e1 : (∫ a, g a * (fun _ : α => (1 : ℝ)) a ∂(μ.restrict s)) = ∫ x in s, g x ∂μ := by
    simp
  have e2 : (∫ a, g a ^ (2 : ℝ) ∂(μ.restrict s)) = ∫ x in s, g x ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact Real.rpow_two (g x)
  have e3 : (∫ a, (1 : ℝ) ^ (2 : ℝ) ∂(μ.restrict s)) = (μ s).toReal := by
    rw [Real.one_rpow, integral_const, Measure.real_def,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    simp
  rw [e1, e2, e3] at hHold
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHold
  calc ∫ x in s, g x ∂μ
      ≤ Real.sqrt (∫ x in s, g x ^ 2 ∂μ) * Real.sqrt (μ s).toReal := hHold
    _ = Real.sqrt (μ s).toReal * Real.sqrt (∫ x in s, g x ^ 2 ∂μ) := mul_comm _ _

end Commons.Analysis.Integral