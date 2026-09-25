import Mathlib

/-!
# Young's convolution inequality for counting measure on `ℤ`

For `p ≥ 1` and `ℝ≥0∞`-valued sequences `a g : ℤ → ℝ≥0∞`,

`∑ₙ (∑ₖ a k * g (n - k))^p ≤ (∑ₖ a k)^p * ∑ₙ (g n)^p`

i.e. `‖a * g‖_{ℓᵖ} ≤ ‖a‖_{ℓ¹} ‖g‖_{ℓᵖ}` (Young's inequality, `q = 1`).

The proof is the classical one: the "weighted power mean" (Hölder) bound
`(∑ₖ a k * x k)^p ≤ (∑ₖ a k)^(p-1) * ∑ₖ a k * (x k)^p` at each `n`, followed by
Tonelli's theorem and the translation invariance of the series on `ℤ`.
-/

namespace Work.IonescuWainger

open MeasureTheory ENNReal
open scoped BigOperators ENNReal

/-- Translation invariance of an `ℝ≥0∞`-valued series over `ℤ`. -/
private lemma tsum_sub_right (g : ℤ → ℝ≥0∞) (k : ℤ) :
    (∑' n : ℤ, g (n - k)) = ∑' n : ℤ, g n := by
  simpa using (Equiv.subRight k).tsum_eq g

/-- Translation invariance of the series of `p`-th powers. -/
private lemma tsum_sub_right_pow (g : ℤ → ℝ≥0∞) (p : ℝ) (k : ℤ) :
    (∑' n : ℤ, (g (n - k)) ^ p) = ∑' n : ℤ, (g n) ^ p :=
  tsum_sub_right (fun m => (g m) ^ p) k

/-- The pointwise algebraic identity underlying the weighted Hölder bound:
`(a x^p)^(1/p) · a^((p-1)/p) = a x` for `p > 1`. -/
private lemma rpow_split {p : ℝ} (hp : 1 < p) (a x : ℝ≥0∞) :
    (a * x ^ p) ^ (1 / p) * a ^ ((p - 1) / p) = a * x := by
  have h1 : p * (1 / p) = 1 := by field_simp
  have h2 : 1 / p + (p - 1) / p = 1 := by field_simp; ring
  calc (a * x ^ p) ^ (1 / p) * a ^ ((p - 1) / p)
      = a ^ (1 / p) * (x ^ p) ^ (1 / p) * a ^ ((p - 1) / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    _ = a ^ (1 / p) * x ^ (p * (1 / p)) * a ^ ((p - 1) / p) := by rw [ENNReal.rpow_mul]
    _ = a ^ (1 / p) * x * a ^ ((p - 1) / p) := by rw [h1, ENNReal.rpow_one]
    _ = (a ^ (1 / p) * a ^ ((p - 1) / p)) * x := by ac_rfl
    _ = a ^ (1 / p + (p - 1) / p) * x := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    _ = a * x := by rw [h2, ENNReal.rpow_one]

/-- Raising the Hölder bound to the power `p`: `(y^(1/p) · a^((p-1)/p))^p = y · a^(p-1)`. -/
private lemma rpow_mul_split {p : ℝ} (hp : 1 < p) (y a : ℝ≥0∞) :
    (y ^ (1 / p) * a ^ ((p - 1) / p)) ^ p = y * a ^ (p - 1) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (1 / p) * p = 1 := by field_simp
  have h2 : ((p - 1) / p) * p = p - 1 := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp0)]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  rw [h1, h2, ENNReal.rpow_one]

/-- `x^(p-1) * x = x^p` for `p ≥ 1`. -/
private lemma rpow_sub_one_mul {p : ℝ} (hp : 1 ≤ p) (x : ℝ≥0∞) :
    x ^ (p - 1) * x = x ^ p := by
  rcases eq_or_lt_of_le hp with rfl | hp'
  · simp
  · calc x ^ (p - 1) * x = x ^ (p - 1) * x ^ 1 := by rw [ENNReal.rpow_one]
      _ = x ^ ((p - 1) + 1) :=
        (ENNReal.rpow_add_of_nonneg (p - 1) 1 (by linarith) (by norm_num)).symm
      _ = x ^ p := by rw [show (p - 1) + 1 = p by ring]

/-- **Weighted power mean / Hölder bound**: for `p ≥ 1` and nonnegative sequences `a`, `x`,
`(∑ₖ a k x k)^p ≤ (∑ₖ a k)^(p-1) ∑ₖ a k x k^p`. -/
private lemma tsum_mul_rpow_le {p : ℝ} (hp : 1 ≤ p) (a x : ℤ → ℝ≥0∞) :
    (∑' k : ℤ, a k * x k) ^ p
      ≤ (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, a k * (x k) ^ p := by
  rcases eq_or_lt_of_le hp with rfl | hp'
  · simp
  · have hp0 : (0 : ℝ) < p := by linarith
    have hα : (0 : ℝ) ≤ 1 / p := by positivity
    have hβ : (0 : ℝ) ≤ (p - 1) / p := by positivity
    have hαβ : 1 / p + (p - 1) / p = 1 := by field_simp; ring
    have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := (Measure.count : Measure ℤ))
      (f := fun k : ℤ => a k * (x k) ^ p) (g := fun k : ℤ => a k)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
      hα hβ hαβ
    simp only [MeasureTheory.lintegral_count] at hholder
    have hL : (∑' k : ℤ, (a k * (x k) ^ p) ^ (1 / p) * (a k) ^ ((p - 1) / p))
        = ∑' k : ℤ, a k * x k :=
      tsum_congr fun k => rpow_split hp' (a k) (x k)
    rw [hL] at hholder
    calc (∑' k : ℤ, a k * x k) ^ p
        ≤ ((∑' k : ℤ, a k * (x k) ^ p) ^ (1 / p)
              * (∑' k : ℤ, a k) ^ ((p - 1) / p)) ^ p :=
          ENNReal.rpow_le_rpow hholder (le_of_lt hp0)
      _ = (∑' k : ℤ, a k * (x k) ^ p) * (∑' k : ℤ, a k) ^ (p - 1) :=
          rpow_mul_split hp' _ _
      _ = (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, a k * (x k) ^ p := mul_comm _ _

theorem young_count_lp {p : ℝ} (hp : 1 ≤ p) (a : ℤ → ENNReal) (g : ℤ → ENNReal) :
    ∑' n : ℤ, (∑' k : ℤ, a k * g (n - k)) ^ p
      ≤ (∑' k : ℤ, a k) ^ p * ∑' n : ℤ, (g n) ^ p := by
  have key : ∀ n : ℤ, (∑' k : ℤ, a k * g (n - k)) ^ p
      ≤ (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, a k * g (n - k) ^ p :=
    fun n => tsum_mul_rpow_le hp a (fun k => g (n - k))
  calc ∑' n : ℤ, (∑' k : ℤ, a k * g (n - k)) ^ p
      ≤ ∑' n : ℤ, (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, a k * g (n - k) ^ p :=
        ENNReal.tsum_le_tsum key
    _ = (∑' k : ℤ, a k) ^ (p - 1) * ∑' n : ℤ, ∑' k : ℤ, a k * g (n - k) ^ p :=
        ENNReal.tsum_mul_left
    _ = (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, ∑' n : ℤ, a k * g (n - k) ^ p := by
        rw [ENNReal.tsum_comm]
    _ = (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, a k * ∑' n : ℤ, g (n - k) ^ p := by
        simp only [ENNReal.tsum_mul_left]
    _ = (∑' k : ℤ, a k) ^ (p - 1) * ∑' k : ℤ, a k * ∑' n : ℤ, (g n) ^ p := by
        refine congrArg (fun z => (∑' k : ℤ, a k) ^ (p - 1) * z) ?_
        refine tsum_congr fun k => ?_
        rw [tsum_sub_right_pow g p k]
    _ = (∑' k : ℤ, a k) ^ (p - 1) * ((∑' k : ℤ, a k) * ∑' n : ℤ, (g n) ^ p) := by
        rw [ENNReal.tsum_mul_right]
    _ = (∑' k : ℤ, a k) ^ p * ∑' n : ℤ, (g n) ^ p := by
        rw [← mul_assoc, rpow_sub_one_mul hp]

end Work.IonescuWainger
