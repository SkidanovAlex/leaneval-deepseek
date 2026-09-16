import Mathlib
import Submission.Commons.Analysis.ExponentialSums.third_derivative_test

open Complex
open scoped BigOperators

namespace Commons.Analysis.ExponentialSums

lemma norm_ch_eq_one (x : ℝ) : ‖ch x‖ = 1 := by
  unfold ch
  rw [Complex.norm_exp_ofReal_mul_I]

lemma ch_nat_mul (t : ℝ) (n : ℕ) : ch ((n : ℝ) * t) = ch t ^ n := by
  unfold ch
  have h : ((2 * Real.pi * ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I
      = (n : ℂ) * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul]

/-- The core trigonometric separation bound: if `t` is at distance `≥ c` from
every integer and `c ≤ 1/2`, then `2c ≤ |sin (π t)|`. -/
lemma two_mul_le_abs_sin_pi (t c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hsep : ∀ k : ℤ, c ≤ |t - k|) : 2 * c ≤ |Real.sin (Real.pi * t)| := by
  set k : ℤ := round t with hk
  set u : ℝ := t - k with hu
  have hd1 : |u| ≤ 1 / 2 := by
    rw [hu]; exact abs_sub_round t
  have hd2 : c ≤ |u| := by
    rw [hu, hk]; exact hsep (round t)
  have hsin : Real.sin (Real.pi * t)
      = (-1 : ℝ) ^ k * Real.sin (Real.pi * u) := by
    have harg : Real.pi * t = Real.pi * u + k * Real.pi := by
      rw [hu]; ring
    rw [harg, Real.sin_add_int_mul_pi]
  rw [hsin, abs_mul]
  have hone : |(-1 : ℝ) ^ k| = 1 := by
    rw [abs_zpow]; simp
  rw [hone, one_mul]
  have hpiu : |Real.pi * u| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [hd1, Real.pi_pos]
  have hid : |Real.sin (Real.pi * u)| = Real.sin (Real.pi * |u|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hpiu, abs_mul, abs_of_pos Real.pi_pos]
  rw [hid]
  have hlow : 2 * |u| ≤ Real.sin (Real.pi * |u|) := by
    have h := Real.mul_le_sin (x := Real.pi * |u|) (by positivity)
      (by nlinarith [hd1, Real.pi_pos])
    have he : (2 / Real.pi) * (Real.pi * |u|) = 2 * |u| := by field_simp
    linarith [h, he]
  nlinarith [hd2, hlow]

lemma geom_sum_Icc_mul (z : ℂ) (N : ℕ) :
    (1 - z) * ∑ n ∈ Finset.Icc 1 N, z ^ n = z - z ^ (N + 1) := by
  induction N with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0)]
    simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]
    rw [mul_add, ih, pow_succ]
    ring

theorem norm_geom_sum_le {N : ℕ} {t c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hsep : ∀ k : ℤ, c ≤ |t - k|) :
    ‖∑ n ∈ Finset.Icc 1 N, ch (n * t)‖ ≤ 1 / (2 * c) := by
  set z : ℂ := ch t with hz
  have hterm : ∀ n ∈ Finset.Icc 1 N, ch ((n : ℝ) * t) = z ^ n := by
    intro n _
    rw [hz]
    exact ch_nat_mul t n
  have hsum : ∑ n ∈ Finset.Icc 1 N, ch ((n : ℝ) * t) = ∑ n ∈ Finset.Icc 1 N, z ^ n :=
    Finset.sum_congr rfl hterm
  have hgeom := geom_sum_Icc_mul z N
  have hz1 : ‖z‖ = 1 := by rw [hz]; exact norm_ch_eq_one t
  have hsinbound : 2 * c ≤ |Real.sin (Real.pi * t)| := two_mul_le_abs_sin_pi t c hc hc2 hsep
  have h1z : ‖1 - z‖ = 2 * |Real.sin (Real.pi * t)| := by
    rw [hz]
    unfold ch
    rw [show ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
          = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by ring]
    rw [norm_sub_rev]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * t)]
    have harg : (2 * Real.pi * t) / 2 = Real.pi * t := by ring
    rw [harg, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hnorm : ‖1 - z‖ * ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ ≤ 2 := by
    have h1 : ‖(1 - z) * ∑ n ∈ Finset.Icc 1 N, z ^ n‖
        = ‖1 - z‖ * ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ := norm_mul _ _
    rw [← h1, hgeom]
    calc ‖z - z ^ (N + 1)‖ ≤ ‖z‖ + ‖z ^ (N + 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz1, one_pow]; norm_num
  have h4c : 4 * c ≤ ‖1 - z‖ := by
    rw [h1z]; nlinarith [hsinbound]
  have hSc : ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ * (4 * c) ≤ 2 := by
    have : ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ * (4 * c)
        ≤ ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ * ‖1 - z‖ :=
      mul_le_mul_of_nonneg_left h4c (norm_nonneg _)
    calc ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ * (4 * c)
        ≤ ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ * ‖1 - z‖ := this
      _ = ‖1 - z‖ * ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ := by ring
      _ ≤ 2 := hnorm
  have hS : ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ ≤ 2 / (4 * c) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * c)]
    exact hSc
  have hfin : 2 / (4 * c) = 1 / (2 * c) := by
    field_simp; norm_num
  rw [hsum, ← hfin]
  exact hS

end Commons.Analysis.ExponentialSums
