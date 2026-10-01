import Mathlib
import Submission.Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt

namespace Work.ZeroDensity.Montgomery

open MeasureTheory intervalIntegral

/-- For nonnegative `A` and `B`, `√(√A · √B) = A^{1/4} · B^{1/4}`. -/
lemma sqrt_sqrt_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (Real.sqrt A * Real.sqrt B) = A ^ ((1 : ℝ) / 4) * B ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_mul (Real.sqrt_nonneg A), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hA, ← Real.rpow_mul hB]
  norm_num

/-- **Weighted Cauchy–Schwarz with a fourth power on one side.** For continuous nonnegative
`f g : ℝ → ℝ` and `a ≤ b`,
`∫_a^b f·g ≤ (b - a)^{1/4} (∫_a^b f^4)^{1/4} (∫_a^b g^2)^{1/2}`
(real powers of the nonnegative integrals). -/
theorem integralMulFourthBound {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, f x * g x
      ≤ (b - a) ^ ((1 : ℝ) / 4) * (∫ x in a..b, f x ^ 4) ^ ((1 : ℝ) / 4)
          * (∫ x in a..b, g x ^ 2) ^ ((1 : ℝ) / 2) := by
  have hI4nn : 0 ≤ ∫ x in a..b, f x ^ 4 :=
    integral_nonneg_of_forall hab (fun u => pow_nonneg (hf0 u) 4)
  have hLnn : 0 ≤ b - a := sub_nonneg.mpr hab
  -- Cauchy--Schwarz applied to `f` and `g`
  have hA : ∫ x in a..b, f x * g x
      ≤ Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) :=
    integralMulLeSqrtMulSqrt hf hg hf0 hg0 hab
  -- Cauchy--Schwarz applied to `f ^ 2` and the constant function `1`
  have hCS2 : ∫ x in a..b, f x ^ 2
      ≤ Real.sqrt (∫ x in a..b, f x ^ 4) * Real.sqrt (b - a) := by
    have h := integralMulLeSqrtMulSqrt (f := fun x => f x ^ 2) (k := fun _ => (1 : ℝ))
      (hf.pow 2) continuous_const (fun x => pow_nonneg (hf0 x) 2) (fun _ => zero_le_one) hab
    have e1 : (∫ x in a..b, (fun x => f x ^ 2) x * (fun _ => (1 : ℝ)) x)
        = ∫ x in a..b, f x ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _
      show f x ^ 2 * (1 : ℝ) = f x ^ 2
      ring
    have e2 : (∫ x in a..b, (fun x => f x ^ 2) x ^ 2) = ∫ x in a..b, f x ^ 4 := by
      apply intervalIntegral.integral_congr
      intro x _
      show (f x ^ 2) ^ 2 = f x ^ 4
      ring
    have e3 : (∫ x in a..b, (fun _ => (1 : ℝ)) x ^ 2) = b - a := by
      have h1 : (∫ x in a..b, (fun _ => (1 : ℝ)) x ^ 2) = ∫ _ in a..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x _
        show (1 : ℝ) ^ 2 = 1
        norm_num
      rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [e1, e2, e3] at h
    exact h
  -- taking square roots
  have hRoot : Real.sqrt (∫ x in a..b, f x ^ 2)
      ≤ (b - a) ^ ((1 : ℝ) / 4) * (∫ x in a..b, f x ^ 4) ^ ((1 : ℝ) / 4) := by
    have h1 : Real.sqrt (∫ x in a..b, f x ^ 2)
        ≤ Real.sqrt (Real.sqrt (∫ x in a..b, f x ^ 4) * Real.sqrt (b - a)) :=
      Real.sqrt_le_sqrt hCS2
    refine h1.trans (le_of_eq ?_)
    rw [mul_comm (Real.sqrt (∫ x in a..b, f x ^ 4)), sqrt_sqrt_mul hLnn hI4nn]
  calc ∫ x in a..b, f x * g x
      ≤ Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := hA
    _ ≤ ((b - a) ^ ((1 : ℝ) / 4) * (∫ x in a..b, f x ^ 4) ^ ((1 : ℝ) / 4))
          * Real.sqrt (∫ x in a..b, g x ^ 2) :=
        mul_le_mul_of_nonneg_right hRoot (Real.sqrt_nonneg _)
    _ = (b - a) ^ ((1 : ℝ) / 4) * (∫ x in a..b, f x ^ 4) ^ ((1 : ℝ) / 4)
          * (∫ x in a..b, g x ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]

end Work.ZeroDensity.Montgomery
