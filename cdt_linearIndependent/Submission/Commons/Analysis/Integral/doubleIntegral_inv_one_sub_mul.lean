import Mathlib
import Submission.Commons.Analysis.Integral.integral_tsum_interval
import Submission.Commons.Analysis.Integral.squareInverseKernelDoubleIntegral

/-!
# `doubleIntegral_inv_one_sub_mul`

The iterated integral over the unit square of `1/(1 - s·t)` equals the series
`∑ₙ 1/(n+1)²`.

Mathematical route: for `0 ≤ s < 1` and `t ∈ [0,1]` we have `|s·t| ≤ s < 1`, so
the geometric series `∑ₙ (s·t)ⁿ` converges to `1/(1 - s·t)`.  Termwise
integration in `t` (`integral_tsum_interval`) gives

    ∫₀¹ 1/(1 - s·t) dt = ∑ₙ sⁿ/(n+1)   for every `0 ≤ s < 1`,

hence almost everywhere in `s`.  Termwise integration in `s` then gives

    ∫₀¹ ∑ₙ sⁿ/(n+1) ds = ∑ₙ 1/(n+1)².

The single point `s = 1` is immaterial for the (Lebesgue) outer integral.
-/

noncomputable section

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped Interval BigOperators

/-- Positivity/summability helper: `∑ₙ sⁿ/(n+1)` converges for `0 ≤ s < 1`. -/
lemma summable_pow_div_succ {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ => s ^ n / ((n : ℝ) + 1)) := by
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => s ^ n)
  · intro n
    positivity
  · intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact div_le_self (pow_nonneg hs0 n) h1
  · exact summable_geometric_of_lt_one hs0 hs1

/-- `∫₀¹ (s·t)ⁿ dt = sⁿ/(n+1)`. -/
lemma intervalIntegral_mul_pow (s : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (s * t) ^ n) = s ^ n / ((n : ℝ) + 1) := by
  calc
    (∫ t in (0 : ℝ)..1, (s * t) ^ n)
        = ∫ t in (0 : ℝ)..1, s ^ n * t ^ n := by
          apply intervalIntegral.integral_congr
          intro t ht
          change (s * t) ^ n = s ^ n * t ^ n
          exact mul_pow s t n
    _ = s ^ n * (∫ t in (0 : ℝ)..1, t ^ n) := by
          rw [intervalIntegral.integral_const_mul]
    _ = s ^ n / ((n : ℝ) + 1) := by
          rw [intervalIntegral_pow_zero_one]
          ring

/-- Normed companion of `intervalIntegral_mul_pow` on `[0,1]`. -/
lemma intervalIntegral_norm_mul_pow {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖(s * t) ^ n‖) = s ^ n / ((n : ℝ) + 1) := by
  have h : (∫ t in (0 : ℝ)..1, ‖(s * t) ^ n‖) =
      ∫ t in (0 : ℝ)..1, (s * t) ^ n := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    change ‖(s * t) ^ n‖ = (s * t) ^ n
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (mul_nonneg hs0 ht.1) n)]
  rw [h, intervalIntegral_mul_pow]

/-- **Inner integral.** For `0 ≤ s < 1`, `∫₀¹ 1/(1 - s·t) dt = ∑ₙ sⁿ/(n+1)`. -/
lemma innerIntegral_eq_tsum {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ t in (0 : ℝ)..1, (1 - s * t)⁻¹) = ∑' n : ℕ, s ^ n / ((n : ℝ) + 1) := by
  have hgeom : (∫ t in (0 : ℝ)..1, (1 - s * t)⁻¹) =
      ∫ t in (0 : ℝ)..1, ∑' n : ℕ, (s * t) ^ n := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hlt : ‖s * t‖ < 1 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0, abs_of_nonneg ht.1]
      calc
        s * t ≤ s * 1 := mul_le_mul_of_nonneg_left ht.2 hs0
        _ = s := mul_one s
        _ < 1 := hs1
    exact (tsum_geometric_of_norm_lt_one hlt).symm
  have hf : ∀ n : ℕ, IntervalIntegrable (fun t : ℝ => (s * t) ^ n) volume (0 : ℝ) 1 :=
    fun n => Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
  have hsum : Summable (fun n : ℕ => ∫ t in (0 : ℝ)..1, ‖(s * t) ^ n‖) :=
    (summable_pow_div_succ hs0 hs1).congr
      (fun n => (intervalIntegral_norm_mul_pow hs0 n).symm)
  have hswap :=
    (integral_tsum_interval (f := fun n t => (s * t) ^ n) hf hsum).symm
  rw [hgeom, hswap]
  apply tsum_congr
  intro n
  exact intervalIntegral_mul_pow s n

/-- `∑ₙ 1/(n+1)²` is summable (shifted `p`-series). -/
lemma summable_one_div_succ_sq :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1 : ℕ) < 2)
  have hinj : Function.Injective (fun k : ℕ => k + 1) :=
    fun a b h => Nat.add_right_cancel h
  have hcomp := hs.comp_injective hinj
  refine hcomp.congr (fun k => ?_)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]

/-- `∫₀¹ sⁿ/(n+1) ds = 1/(n+1)²`. -/
lemma intervalIntegral_pow_div_succ (n : ℕ) :
    (∫ s in (0 : ℝ)..1, s ^ n / ((n : ℝ) + 1)) =
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have hrw : (fun s : ℝ => s ^ n / ((n : ℝ) + 1)) =
      fun s : ℝ => ((n : ℝ) + 1)⁻¹ * s ^ n := by
    funext s
    rw [div_eq_inv_mul]
  rw [hrw, intervalIntegral.integral_const_mul, intervalIntegral_pow_zero_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Normed companion of `intervalIntegral_pow_div_succ` on `[0,1]`. -/
lemma intervalIntegral_norm_pow_div_succ (n : ℕ) :
    (∫ s in (0 : ℝ)..1, ‖s ^ n / ((n : ℝ) + 1)‖) =
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have h : (∫ s in (0 : ℝ)..1, ‖s ^ n / ((n : ℝ) + 1)‖) =
      ∫ s in (0 : ℝ)..1, s ^ n / ((n : ℝ) + 1) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    change ‖s ^ n / ((n : ℝ) + 1)‖ = s ^ n / ((n : ℝ) + 1)
    have hnn : (0 : ℝ) ≤ s ^ n / ((n : ℝ) + 1) :=
      div_nonneg (pow_nonneg hs.1 n) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [h, intervalIntegral_pow_div_succ]

/-- **Outer integral.** `∫₀¹ ∑ₙ sⁿ/(n+1) ds = ∑ₙ 1/(n+1)²`. -/
lemma outerIntegral_eq_tsum :
    (∫ s in (0 : ℝ)..1, ∑' n : ℕ, s ^ n / ((n : ℝ) + 1)) =
      ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have hf : ∀ n : ℕ, IntervalIntegrable (fun s : ℝ => s ^ n / ((n : ℝ) + 1)) volume
      (0 : ℝ) 1 :=
    fun n => Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
  have hsum : Summable (fun n : ℕ => ∫ s in (0 : ℝ)..1, ‖s ^ n / ((n : ℝ) + 1)‖) :=
    summable_one_div_succ_sq.congr
      (fun n => (intervalIntegral_norm_pow_div_succ n).symm)
  have hswap :=
    (integral_tsum_interval (f := fun n s => s ^ n / ((n : ℝ) + 1)) hf hsum).symm
  rw [hswap]
  apply tsum_congr
  intro n
  exact intervalIntegral_pow_div_succ n

/-- **The requested identity.** -/
theorem doubleIntegral_inv_one_sub_mul :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, (1 - s * t)⁻¹)
      = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have hcongr : (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, (1 - s * t)⁻¹) =
      ∫ s in (0 : ℝ)..1, ∑' n : ℕ, s ^ n / ((n : ℝ) + 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with s hsne
    intro hsI
    have hsI' : s ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hsI
    have hs0 : 0 < s := hsI'.1
    have hs1 : s ≤ 1 := hsI'.2
    have hslt : s < 1 := lt_of_le_of_ne hs1 hsne
    exact innerIntegral_eq_tsum (le_of_lt hs0) hslt
  rw [hcongr, outerIntegral_eq_tsum]

end Commons.Analysis.Integral
