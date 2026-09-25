import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re

open Complex Filter Metric Set
open scoped Topology BigOperators
noncomputable section

namespace Commons.NumberTheory.Zeta

/-- For `w ≠ 1`, `‖riemannZeta₁ w‖ = ‖w - 1‖ · ‖riemannZeta w‖`. -/
private lemma zeta1_norm_eq_mul_d4 (w : ℂ) (hw : w ≠ 1) :
    ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
  have h1 : (w - 1) * riemannZeta w = riemannZeta₁ w := by
    calc
      (w - 1) * riemannZeta w = (w - 1) * ((w - 1)⁻¹ * riemannZeta₁ w) := by
        rw [riemannZeta_eq_inv_sub_mul hw]
      _ = riemannZeta₁ w := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hw)]
        simp
  calc
    ‖riemannZeta₁ w‖ = ‖(w - 1) * riemannZeta w‖ := by rw [← h1]
    _ = ‖w - 1‖ * ‖riemannZeta w‖ := by rw [norm_mul]

/-- Polynomial growth of `riemannZeta₁` on the closed disk of radius `4` about `2 + I*t`,
for `|t| ≥ 5`. The disk has real part in `[-2,6]` and imaginary part within `4` of `t`,
so it is covered by the left strip bounds on `ζ` and the half-plane `re ≥ 3`. -/
theorem zeta1_growth_disk4 :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 5 ≤ |t| → ∀ w : ℂ,
      ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ 4 → ‖riemannZeta₁ w‖ ≤ C * (|t| + 7) ^ 15 := by
  rcases zeta_strip_polyGrowth with ⟨Cpg, hCpg0, hCpg⟩
  rcases zeta_strip_polyGrowth_neg with ⟨Cng, hCng0, hCng⟩
  rcases zeta_norm_le_const_of_three_le_re with ⟨C3, hC30, hC3⟩
  refine ⟨max Cpg (max Cng C3), lt_max_of_lt_left hCpg0, ?_⟩
  intro t ht w hball
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hball' : ‖w - c‖ ≤ 4 := hball
  have hσdist : |w.re - 2| ≤ ‖w - c‖ := by
    have h := Complex.abs_re_le_norm (w - c)
    simpa [c] using h
  have hτdist : |w.im - t| ≤ ‖w - c‖ := by
    have h := Complex.abs_im_le_norm (w - c)
    simpa [c] using h
  have hσ4 : |w.re - 2| ≤ 4 := le_trans hσdist hball'
  have hτ4 : |w.im - t| ≤ 4 := le_trans hτdist hball'
  have hσlo : -2 ≤ w.re := by have h := (abs_le.mp hσ4).1; linarith
  have hτge : 1 ≤ |w.im| := by
    have h2 : |t| ≤ |w.im| + |w.im - t| := by
      calc |t| = |w.im + (t - w.im)| := by congr 1; ring
        _ ≤ |w.im| + |t - w.im| := abs_add_le _ _
        _ = |w.im| + |w.im - t| := by rw [abs_sub_comm]
    linarith
  have hτhi : |w.im| ≤ |t| + 4 := by
    have h2 : |w.im| ≤ |w.im - t| + |t| := by
      calc |w.im| = |(w.im - t) + t| := by congr 1; ring
        _ ≤ |w.im - t| + |t| := abs_add_le _ _
    linarith
  have hw_ne1 : w ≠ 1 := by
    intro hw1
    have hle : ‖(1 : ℂ) - c‖ ≤ 4 := by
      have h' : ‖w - c‖ ≤ 4 := hball'
      rw [hw1] at h'
      exact h'
    have him : |t| ≤ ‖(1 : ℂ) - c‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - c)
      have hval : ((1 : ℂ) - c).im = -t := by simp only [c]; simp
      rw [hval, abs_neg] at h
      exact h
    linarith
  have hζ : ‖riemannZeta w‖ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 := by
    have hwform : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
      apply Complex.ext <;> simp
    have hbase : (1 : ℝ) ≤ |w.im| + 3 := by linarith [abs_nonneg w.im]
    have hEqZeta : riemannZeta w = riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ)) :=
      congrArg riemannZeta hwform
    by_cases hσ3 : w.re ≤ 3
    · by_cases hσm1 : -1 ≤ w.re
      · have h := hCpg w.re w.im hσm1 hσ3 hτge
        have hpow : (|w.im| + 3) ^ 4 ≤ (|w.im| + 3) ^ 12 :=
          pow_le_pow_right₀ hbase (by norm_num)
        calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ := by
              rw [hEqZeta]
          _ ≤ Cpg * (|w.im| + 3) ^ 4 := h
          _ ≤ Cpg * (|w.im| + 3) ^ 12 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCpg0)
          _ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · have hσm1' : w.re ≤ -1 := le_of_lt (lt_of_not_ge hσm1)
        have h := hCng w.re w.im hσlo hσm1' hτge
        have hCng_le : Cng ≤ max Cpg (max Cng C3) :=
          le_trans (le_max_left Cng C3) (le_max_right Cpg (max Cng C3))
        calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ := by
              rw [hEqZeta]
          _ ≤ Cng * (|w.im| + 3) ^ 12 := h
          _ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 :=
              mul_le_mul_of_nonneg_right hCng_le (by positivity)
    · have hσ3' : 3 ≤ w.re := le_of_lt (lt_of_not_ge hσ3)
      have h := hC3 w hσ3'
      have hC3_le : C3 ≤ max Cpg (max Cng C3) :=
        le_trans (le_max_right Cng C3) (le_max_right Cpg (max Cng C3))
      have hge1 : (1 : ℝ) ≤ (|w.im| + 3) ^ 12 := one_le_pow₀ hbase
      calc ‖riemannZeta w‖ ≤ C3 := h
        _ = C3 * 1 := by ring
        _ ≤ C3 * (|w.im| + 3) ^ 12 := mul_le_mul_of_nonneg_left hge1 (le_of_lt hC30)
        _ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 :=
            mul_le_mul_of_nonneg_right hC3_le (by positivity)
  have hc1 : ‖c - 1‖ ≤ 1 + |t| := by
    have hrew : c - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by
      simp only [c]; ring
    rw [hrew]
    calc ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
          norm_add_le _ _
      _ = 1 + |t| := by
        rw [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        ring
  have hw1le : ‖w - 1‖ ≤ |t| + 6 := by
    have hsum : (w - c) + (c - 1) = w - 1 := by ring
    calc ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by rw [← hsum]
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 4 + (1 + |t|) := by linarith
      _ ≤ |t| + 6 := by linarith
  have hCz0 : 0 < max Cpg (max Cng C3) := lt_max_of_lt_left hCpg0
  have hτ_le : |w.im| + 3 ≤ |t| + 7 := by linarith
  have hpow : (|w.im| + 3) ^ 12 ≤ (|t| + 7) ^ 12 :=
    pow_le_pow_left₀ (by positivity) hτ_le 12
  have ht7nn : 0 ≤ |t| + 7 := by linarith [abs_nonneg t]
  calc ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := zeta1_norm_eq_mul_d4 w hw_ne1
    _ ≤ (|t| + 6) * (max Cpg (max Cng C3) * (|w.im| + 3) ^ 12) :=
        mul_le_mul hw1le hζ (by positivity) (by positivity)
    _ ≤ (|t| + 7) * (max Cpg (max Cng C3) * (|w.im| + 3) ^ 12) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) (by positivity)
    _ ≤ (|t| + 7) * (max Cpg (max Cng C3) * (|t| + 7) ^ 12) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hCz0)) (by linarith [abs_nonneg t])
    _ = max Cpg (max Cng C3) * (|t| + 7) ^ 13 := by ring
    _ ≤ max Cpg (max Cng C3) * (|t| + 7) ^ 15 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hCz0)
        exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)

end Commons.NumberTheory.Zeta
