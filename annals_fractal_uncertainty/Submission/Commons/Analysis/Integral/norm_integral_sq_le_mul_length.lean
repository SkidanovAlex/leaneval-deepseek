import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace Commons.Analysis.Integral

/-- (C-S on an interval for a continuous real integrand) `(∫_a^b g)² ≤ (b−a)·∫_a^b g²`. -/
private lemma interval_sq_le_length {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hgcont : Continuous g) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, (g x) ^ 2) := by
  by_cases hba : a = b
  · subst b
    simp
  have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab hba)
  let I : ℝ := ∫ x in a..b, g x
  let c : ℝ := I / (b - a)
  have hpt : ∀ x, (g x - c) ^ 2 = (g x) ^ 2 - 2 * c * g x + c ^ 2 := by
    intro x
    ring
  have hc2 : (∫ x in a..b, c ^ 2) = (b - a) * c ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp
  have hint0 : 0 ≤ ∫ x in a..b, (g x - c) ^ 2 := by
    exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg (g x - c))
  have hInt1 : IntervalIntegrable g volume a b := hgcont.intervalIntegrable a b
  have hInt2 : IntervalIntegrable (fun x : ℝ => (g x) ^ 2) volume a b :=
    hgcont.pow 2 |>.intervalIntegrable a b
  have hInt5 : IntervalIntegrable (fun x : ℝ => 2 * c * g x) volume a b :=
    (continuous_const.mul hgcont).intervalIntegrable a b
  have hIntC : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume a b := intervalIntegrable_const
  have hIntA : IntervalIntegrable (fun x : ℝ => (g x) ^ 2 - 2 * c * g x) volume a b :=
    hInt2.sub hInt5
  have hExp : (∫ x in a..b, (g x - c) ^ 2) = (∫ x in a..b, (g x) ^ 2) - 2 * c * I + (b - a) * c ^ 2 := by
    calc
      (∫ x in a..b, (g x - c) ^ 2) = (∫ x in a..b, (g x) ^ 2 - 2 * c * g x + c ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hpt x
      _ = (∫ x in a..b, (g x) ^ 2 - 2 * c * g x) + (∫ x in a..b, c ^ 2) := by
        rw [intervalIntegral.integral_add hIntA hIntC]
      _ = ((∫ x in a..b, (g x) ^ 2) - (∫ x in a..b, 2 * c * g x)) + (∫ x in a..b, c ^ 2) := by
        rw [intervalIntegral.integral_sub hInt2 hInt5]
      _ = (∫ x in a..b, (g x) ^ 2) - 2 * c * I + (b - a) * c ^ 2 := by
        have hInt4 : (∫ x in a..b, 2 * c * g x) = 2 * c * (∫ x in a..b, g x) := by
          rw [intervalIntegral.integral_const_mul (r := (2 * c : ℝ)) (f := fun x : ℝ => g x)]
        rw [hInt4, hc2]
  have hmain0 : 0 ≤ (b - a) * ((∫ x in a..b, (g x) ^ 2) - 2 * c * I + (b - a) * c ^ 2) := by
    exact mul_nonneg (le_of_lt hpos) (by simpa [hExp] using hint0)
  have hfinal : I ^ 2 ≤ (b - a) * (∫ x in a..b, (g x) ^ 2) := by
    dsimp [c] at hmain0
    have hne : b - a ≠ 0 := ne_of_gt hpos
    field_simp [hne] at hmain0
    nlinarith
  change (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, (g x) ^ 2)
  simpa [I] using hfinal

theorem norm_integral_sq_le_mul_length {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : Continuous f) :
    ‖∫ x in a..b, f x‖ ^ 2 ≤ (b - a) * (∫ x in a..b, ‖f x‖ ^ 2) := by
  have hnle : ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, ‖f x‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hcs := interval_sq_le_length hab (g := fun x : ℝ => ‖f x‖) hf.norm
  calc
    ‖∫ x in a..b, f x‖ ^ 2 ≤ (∫ x in a..b, ‖f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnle 2
    _ ≤ (b - a) * (∫ x in a..b, ‖f x‖ ^ 2) := hcs

end Commons.Analysis.Integral