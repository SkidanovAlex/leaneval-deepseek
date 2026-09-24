import Mathlib
import Submission.Work.GM.S3.Defs

namespace Work.GM.S3

/-- **Cauchy–Schwarz for interval integrals.** For continuous nonnegative `f, g` on `[a,b]`,
`∫_{a}^{b} f g ≤ (∫_{a}^{b} f²)^{1/2} (∫_{a}^{b} g²)^{1/2}`.  (Proof: `0 ≤ ∫ (f - t g)²` for all
`t ∈ ℝ`, expand, and take `t = C/B` if `B = ∫ g² > 0`.) -/
theorem integral_mul_le_sqrt_mul_sqrt {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hf0 : ∀ x ∈ Set.Icc a b, 0 ≤ f x) (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) :
    ∫ x in a..b, f x * g x ≤
      Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
  have hf' : ContinuousOn f (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hf
  have hg' : ContinuousOn g (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hg
  have hc_f2 : ContinuousOn (fun x => f x ^ 2) (Set.uIcc a b) := hf'.pow 2
  have hc_g2 : ContinuousOn (fun x => g x ^ 2) (Set.uIcc a b) := hg'.pow 2
  have hc_fg : ContinuousOn (fun x => f x * g x) (Set.uIcc a b) := hf'.mul hg'
  set A : ℝ := ∫ x in a..b, f x ^ 2 with hA
  set B : ℝ := ∫ x in a..b, g x ^ 2 with hB
  set C : ℝ := ∫ x in a..b, f x * g x with hC
  -- Expansion of `∫ (f - t g)^2` as a quadratic in `t`.
  have h_expand : ∀ t : ℝ, ∫ x in a..b, (f x - t * g x) ^ 2 = A - 2 * t * C + t ^ 2 * B := by
    intro t
    have hI6 : IntervalIntegrable (fun x => f x ^ 2 - 2 * t * (f x * g x))
        MeasureTheory.volume a b :=
      (hc_f2.sub (continuousOn_const.mul hc_fg)).intervalIntegrable
    have hI5 : IntervalIntegrable (fun x => t ^ 2 * g x ^ 2) MeasureTheory.volume a b :=
      (continuousOn_const.mul hc_g2).intervalIntegrable
    have hI1 : IntervalIntegrable (fun x => f x ^ 2) MeasureTheory.volume a b :=
      hc_f2.intervalIntegrable
    have hI4 : IntervalIntegrable (fun x => 2 * t * (f x * g x)) MeasureTheory.volume a b :=
      (continuousOn_const.mul hc_fg).intervalIntegrable
    calc ∫ x in a..b, (f x - t * g x) ^ 2
        = ∫ x in a..b, ((f x ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2) := by
          apply intervalIntegral.integral_congr; intro x hx; ring
      _ = (∫ x in a..b, (f x ^ 2 - 2 * t * (f x * g x))) + ∫ x in a..b, t ^ 2 * g x ^ 2 :=
          intervalIntegral.integral_add hI6 hI5
      _ = ((∫ x in a..b, f x ^ 2) - ∫ x in a..b, 2 * t * (f x * g x))
            + ∫ x in a..b, t ^ 2 * g x ^ 2 := by
          rw [intervalIntegral.integral_sub hI1 hI4]
      _ = ((∫ x in a..b, f x ^ 2) - 2 * t * (∫ x in a..b, f x * g x))
            + t ^ 2 * (∫ x in a..b, g x ^ 2) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = A - 2 * t * C + t ^ 2 * B := by rw [← hA, ← hB, ← hC]
  have hA0 : 0 ≤ A := by
    rw [hA]; exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [hB]; exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact intervalIntegral.integral_nonneg hab (fun x hx => mul_nonneg (hf0 x hx) (hg0 x hx))
  -- `∫ (f - t g)^2 ≥ 0` for every real `t`.
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * C + t ^ 2 * B := by
    intro t; rw [← h_expand t]
    exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  rcases lt_or_eq_of_le hB0 with hBpos | hBzero
  · -- Case `B > 0`: evaluate the quadratic at `t = C/B`.
    have hkey : A - C ^ 2 / B ≥ 0 := by
      have h := hquad (C / B)
      have heq : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by
        field_simp
        ring
      linarith [h, heq]
    have hsq : C ^ 2 ≤ A * B := by
      have h' : C ^ 2 / B ≤ A := by linarith
      exact (div_le_iff₀ hBpos).mp h'
    rw [← Real.sqrt_mul hA0 B, Real.le_sqrt hC0 (mul_nonneg hA0 hB0)]
    exact hsq
  · -- Case `B = 0`: the quadratic is affine in `t`, forcing `C ≤ 0`.
    have hBZ : B = 0 := hBzero.symm
    have hCle : C ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have hCne : C ≠ 0 := ne_of_gt hcon
      have h := hquad ((A + 1) / (2 * C))
      have ht : 2 * ((A + 1) / (2 * C)) * C = A + 1 := by
        field_simp
      rw [hBZ] at h
      simp only [mul_zero, add_zero] at h
      linarith [h, ht]
    have hrhs : Real.sqrt A * Real.sqrt B = 0 := by rw [hBZ, Real.sqrt_zero, mul_zero]
    rw [hrhs]
    exact hCle

end Work.GM.S3
