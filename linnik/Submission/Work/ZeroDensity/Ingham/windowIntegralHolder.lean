import Mathlib
import Submission.Work.ZeroDensity.Montgomery.integralMulFourthBound

namespace Work.ZeroDensity.Ingham

open MeasureTheory intervalIntegral

/-- **Three-function Hölder inequality for interval integrals** (exponents `4`, `2`, `4`).

For continuous nonnegative `f g w : ℝ → ℝ` and `A ≤ B`,
`∫_A^B f·g·w ≤ (∫_A^B f⁴)^{1/4} (∫_A^B g²)^{1/2} (∫_A^B w⁴)^{1/4}`.

Obtained by applying Cauchy–Schwarz (`Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt`)
to the pair `(f·w, g)` and again to `(f², w²)`. -/
private lemma windowHolder3 {f g w : ℝ → ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hf : Continuous f) (hg : Continuous g) (hw : Continuous w)
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u) (hw0 : ∀ u, 0 ≤ w u) :
    (∫ u in A..B, f u * g u * w u)
      ≤ (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4) * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2)
          * (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4) := by
  have hfw : Continuous fun u => f u * w u := hf.mul hw
  have hfw0 : ∀ u, 0 ≤ f u * w u := fun u => mul_nonneg (hf0 u) (hw0 u)
  -- Cauchy–Schwarz on the pair `(f·w, g)`
  have hStep1 : (∫ u in A..B, (f u * w u) * g u)
      ≤ Real.sqrt (∫ u in A..B, (f u * w u) ^ 2) * Real.sqrt (∫ u in A..B, g u ^ 2) :=
    Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt hfw hg hfw0 hg0 hAB
  -- Cauchy–Schwarz on the pair `(f², w²)`
  have hStep2 : (∫ u in A..B, f u ^ 2 * w u ^ 2)
      ≤ Real.sqrt (∫ u in A..B, f u ^ 4) * Real.sqrt (∫ u in A..B, w u ^ 4) := by
    have h := Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt
      (f := fun u => f u ^ 2) (k := fun u => w u ^ 2)
      (hf.pow 2) (hw.pow 2) (fun u => pow_nonneg (hf0 u) 2) (fun u => pow_nonneg (hw0 u) 2) hAB
    have e1 : (∫ u in A..B, (fun u => f u ^ 2) u * (fun u => w u ^ 2) u)
        = ∫ u in A..B, f u ^ 2 * w u ^ 2 := rfl
    have e2 : (∫ u in A..B, ((fun u => f u ^ 2) u) ^ 2) = ∫ u in A..B, f u ^ 4 := by
      apply intervalIntegral.integral_congr; intro u _; ring
    have e3 : (∫ u in A..B, ((fun u => w u ^ 2) u) ^ 2) = ∫ u in A..B, w u ^ 4 := by
      apply intervalIntegral.integral_congr; intro u _; ring
    rw [e1, e2, e3] at h
    exact h
  have hsqrt : Real.sqrt (∫ u in A..B, (f u * w u) ^ 2)
      ≤ (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4) * (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4) := by
    have hsq : (∫ u in A..B, (f u * w u) ^ 2) = ∫ u in A..B, f u ^ 2 * w u ^ 2 := by
      apply intervalIntegral.integral_congr; intro u _; ring
    have hmono : Real.sqrt (∫ u in A..B, (f u * w u) ^ 2)
        ≤ Real.sqrt (Real.sqrt (∫ u in A..B, f u ^ 4) * Real.sqrt (∫ u in A..B, w u ^ 4)) := by
      apply Real.sqrt_le_sqrt
      rw [hsq]
      exact hStep2
    refine hmono.trans (le_of_eq ?_)
    exact Work.ZeroDensity.Montgomery.sqrt_sqrt_mul
      (integral_nonneg_of_forall hAB (fun u => pow_nonneg (hf0 u) 4))
      (integral_nonneg_of_forall hAB (fun u => pow_nonneg (hw0 u) 4))
  calc (∫ u in A..B, f u * g u * w u)
      = ∫ u in A..B, (f u * w u) * g u := by
        apply intervalIntegral.integral_congr; intro u _; ring
    _ ≤ Real.sqrt (∫ u in A..B, (f u * w u) ^ 2) * Real.sqrt (∫ u in A..B, g u ^ 2) := hStep1
    _ ≤ ((∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4) * (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4))
          * Real.sqrt (∫ u in A..B, g u ^ 2) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4) * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2)
          * (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow]; ring

/-- **Weight bound for a window function.**  If `0 ≤ w u ≤ W` for all `u` and `A ≤ B`, then
`(∫_A^B w⁴)^{1/4} ≤ W^{3/4} (∫_A^B w)^{1/4}`.  Pointwise `w⁴ = w·w³ ≤ w·W³`, so
`∫ w⁴ ≤ W³ ∫ w`, and the claim follows from monotonicity of `x ↦ x^{1/4}` on `[0,∞)`. -/
private lemma windowWeightBound {w : ℝ → ℝ} {A B W : ℝ} (hAB : A ≤ B) (hW : 0 ≤ W)
    (hw : Continuous w) (hw0 : ∀ u, 0 ≤ w u) (hwle : ∀ u, w u ≤ W) :
    (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4)
      ≤ W ^ ((3 : ℝ) / 4) * (∫ u in A..B, w u) ^ ((1 : ℝ) / 4) := by
  have hpt : ∀ u, w u ^ 4 ≤ W ^ 3 * w u := by
    intro u
    have h3 : w u ^ 3 ≤ W ^ 3 := pow_le_pow_left₀ (hw0 u) (hwle u) 3
    calc w u ^ 4 = w u ^ 3 * w u := by ring
      _ ≤ W ^ 3 * w u := mul_le_mul_of_nonneg_right h3 (hw0 u)
  have hIntMono : (∫ u in A..B, w u ^ 4) ≤ ∫ u in A..B, W ^ 3 * w u :=
    intervalIntegral.integral_mono hAB ((hw.pow 4).intervalIntegrable A B)
      ((continuous_const.mul hw).intervalIntegrable A B) hpt
  have hbase : (∫ u in A..B, w u ^ 4) ≤ W ^ 3 * (∫ u in A..B, w u) := by
    rw [intervalIntegral.integral_const_mul] at hIntMono
    exact hIntMono
  have hbase0 : 0 ≤ (∫ u in A..B, w u ^ 4) :=
    integral_nonneg_of_forall hAB (fun u => pow_nonneg (hw0 u) 4)
  have hW3 : (0 : ℝ) ≤ W ^ 3 := pow_nonneg hW 3
  have hIw : 0 ≤ (∫ u in A..B, w u) := integral_nonneg_of_forall hAB hw0
  calc (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4)
      ≤ (W ^ 3 * (∫ u in A..B, w u)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hbase0 hbase (by norm_num)
    _ = W ^ ((3 : ℝ) / 4) * (∫ u in A..B, w u) ^ ((1 : ℝ) / 4) := by
        have hpow : (W ^ 3) ^ ((1 : ℝ) / 4) = W ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_natCast W 3, ← Real.rpow_mul hW]
          congr 1
          norm_num
        rw [Real.mul_rpow hW3 hIw]
        simp only [hpow]

theorem windowIntegralHolder {f g w : ℝ → ℝ} {A B W : ℝ} (hAB : A ≤ B) (hW : 0 ≤ W)
    (hf : Continuous f) (hg : Continuous g) (hw : Continuous w)
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u) (hw0 : ∀ u, 0 ≤ w u) (hwle : ∀ u, w u ≤ W) :
    (∫ u in A..B, f u * g u * w u)
      ≤ W ^ ((3 : ℝ) / 4) * (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4)
          * (∫ u in A..B, w u) ^ ((1 : ℝ) / 4) * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2) := by
  have h1 := windowHolder3 hAB hf hg hw hf0 hg0 hw0
  have h2 := windowWeightBound hAB hW hw hw0 hwle
  have hf4 : 0 ≤ (∫ u in A..B, f u ^ 4) :=
    integral_nonneg_of_forall hAB (fun u => pow_nonneg (hf0 u) 4)
  have hg2 : 0 ≤ (∫ u in A..B, g u ^ 2) :=
    integral_nonneg_of_forall hAB (fun u => pow_nonneg (hg0 u) 2)
  have hnn : 0 ≤ (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4)
      * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hf4 _) (Real.rpow_nonneg hg2 _)
  calc (∫ u in A..B, f u * g u * w u)
      ≤ (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4) * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2)
          * (∫ u in A..B, w u ^ 4) ^ ((1 : ℝ) / 4) := h1
    _ ≤ (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4) * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2)
          * (W ^ ((3 : ℝ) / 4) * (∫ u in A..B, w u) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left h2 hnn
    _ = W ^ ((3 : ℝ) / 4) * (∫ u in A..B, f u ^ 4) ^ ((1 : ℝ) / 4)
          * (∫ u in A..B, w u) ^ ((1 : ℝ) / 4) * (∫ u in A..B, g u ^ 2) ^ ((1 : ℝ) / 2) := by
        ring

end Work.ZeroDensity.Ingham
