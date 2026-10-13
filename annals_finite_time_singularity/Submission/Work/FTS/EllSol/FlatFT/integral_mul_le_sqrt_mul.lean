import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- Cauchy–Schwarz for integrals of nonnegative functions on `ℝ`: if `a²` and `b²` are
integrable, then so is `a * b`, and `∫ a b ≤ √(∫ a² · ∫ b²)`. -/
theorem integral_mul_le_sqrt_mul (a b : ℝ → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (ha2 : MeasureTheory.Integrable (fun x : ℝ => a x ^ 2))
    (hb2 : MeasureTheory.Integrable (fun x : ℝ => b x ^ 2)) :
    MeasureTheory.Integrable (fun x : ℝ => a x * b x) ∧
      (∫ x : ℝ, a x * b x) ≤ Real.sqrt ((∫ x : ℝ, a x ^ 2) * (∫ x : ℝ, b x ^ 2)) := by
  -- `a` and `b` are a.e. strongly measurable: each is `√(·²)` of a measurable function.
  have hams_a : MeasureTheory.AEStronglyMeasurable a := by
    have h : MeasureTheory.AEStronglyMeasurable (fun x => Real.sqrt (a x ^ 2)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable ha2.aestronglyMeasurable
    have h' : (fun x => Real.sqrt (a x ^ 2)) = a := by
      funext x; rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (ha x)]
    rwa [h'] at h
  have hams_b : MeasureTheory.AEStronglyMeasurable b := by
    have h : MeasureTheory.AEStronglyMeasurable (fun x => Real.sqrt (b x ^ 2)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hb2.aestronglyMeasurable
    have h' : (fun x => Real.sqrt (b x ^ 2)) = b := by
      funext x; rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hb x)]
    rwa [h'] at h
  -- hence `a, b ∈ L²`, so their product is in `L¹`.
  have hma : MeasureTheory.MemLp a 2 (μ := MeasureTheory.volume) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hams_a).2 ha2
  have hmb : MeasureTheory.MemLp b 2 (μ := MeasureTheory.volume) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hams_b).2 hb2
  refine ⟨MeasureTheory.memLp_one_iff_integrable.1 (hma.mul hmb), ?_⟩
  -- Hölder with `p = q = 2`, then `√A · √B = √(A·B)`.
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := MeasureTheory.volume)
    (p := 2) (q := 2) hpq (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (by simpa using hma) (by simpa using hmb)
  -- `hholder` is stated with the real power `x ^ (2 : ℝ)`; the goal uses the natural power.
  have hA : 0 ≤ ∫ x : ℝ, a x ^ (2 : ℝ) :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (ha x) 2)
  have hmain : (∫ x : ℝ, a x * b x) ≤
      Real.sqrt ((∫ x : ℝ, a x ^ (2 : ℝ)) * (∫ x : ℝ, b x ^ (2 : ℝ))) := by
    calc (∫ x : ℝ, a x * b x)
        ≤ (∫ x : ℝ, a x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫ x : ℝ, b x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hholder
      _ = Real.sqrt ((∫ x : ℝ, a x ^ (2 : ℝ)) * (∫ x : ℝ, b x ^ (2 : ℝ))) := by
          rw [Real.sqrt_mul hA, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  exact hmain.trans_eq (congrArg Real.sqrt (by simp))

end Work.FTS.EllSol.FlatFT
