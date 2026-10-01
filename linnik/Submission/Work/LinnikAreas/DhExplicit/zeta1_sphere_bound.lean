import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re

open Complex
open scoped Topology BigOperators

noncomputable section
namespace Work.LinnikAreas.DhExplicit

/-- `ζ₁ = (s-1)ζ` written in terms of `ζ`, away from the pole. -/
private lemma zeta1_eq_mul_of_ne_one (z : ℂ) (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  have h := riemannZeta_eq_inv_sub_mul hz
  rw [h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]

/-- A uniform bound for `ζ₁` on the fixed disk `‖z‖ ≤ 10`. -/
private lemma zeta1_bound_closedBall_ten :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ z : ℂ, ‖z‖ ≤ 10 → ‖riemannZeta₁ z‖ ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 10) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : ℂ) 10).Nonempty := ⟨0, by simp⟩
  obtain ⟨x, hx, hxmax⟩ := hK.exists_isMaxOn hne
    (differentiable_riemannZeta₁.continuous.continuousOn.norm)
  refine ⟨max 1 ‖riemannZeta₁ x‖, le_max_left _ _, fun z hz => ?_⟩
  exact le_trans (hxmax (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz))
    (le_max_right _ _)

/-- Uniform bound for `ζ₁ = (s-1)·ζ` on the circle of radius `5/2` about the centre `2 + t·I`:
there is `K ≥ 1` with `‖ζ₁ z‖ ≤ K · (|t| + 9)^5` for every real `t` and every `z` on that circle.
The circle has `re z ∈ [-1/2, 9/2]`, `|im z - t| ≤ 5/2` and `‖z‖ ≤ |t| + 9/2`, so:
for `|t| ≤ 5` one has `‖z‖ ≤ 10` and compactness of `closedBall 0 10` gives a uniform bound for
`ζ₁` there (note `9^5 ≥ 1`); for `|t| > 5` one has `|im z| ≥ 1` and `z ≠ 1`, so
`‖ζ₁ z‖ = ‖z - 1‖·‖ζ z‖ ≤ (|t| + 5)·‖ζ z‖ ≤ (|t| + 5)·K₁·(|t| + 9)^4 ≤ K₁·(|t| + 9)^5`,
using `Commons.NumberTheory.Zeta.zeta_strip_polyGrowth` for `-1 ≤ re z ≤ 3` and
`Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re` for `3 ≤ re z`. -/
theorem zeta1_sphere_bound : ∃ K : ℝ, 1 ≤ K ∧ ∀ (t : ℝ) (z : ℂ),
    ‖z - ((2 : ℂ) + Complex.I * (t : ℂ))‖ = (5 : ℝ) / 2 →
    ‖riemannZeta₁ z‖ ≤ K * (|t| + 9) ^ 5 := by
  obtain ⟨B0, hB01, hB0⟩ := zeta1_bound_closedBall_ten
  obtain ⟨Cpg, hCpgpos, hCpg⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  obtain ⟨C3, hC3pos, hC3⟩ := Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
  set K1 : ℝ := max Cpg (max C3 1) with hK1def
  have hK11 : 1 ≤ K1 := le_trans (le_max_right C3 1) (le_max_right Cpg (max C3 1))
  have hK1pos : 0 < K1 := lt_of_lt_of_le zero_lt_one hK11
  have hCpgK1 : Cpg ≤ K1 := le_max_left _ _
  have hC3K1 : C3 ≤ K1 := le_trans (le_max_left C3 1) (le_max_right Cpg (max C3 1))
  set K : ℝ := max B0 K1 with hKdef
  have hKle1 : K1 ≤ K := le_max_right B0 K1
  have hKge1 : 1 ≤ K := le_trans hB01 (le_max_left B0 K1)
  refine ⟨K, hKge1, fun t z hz => ?_⟩
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
  by_cases ht5 : |t| ≤ 5
  · -- near case: `‖z‖ ≤ 10`, use compactness
    have hcnorm : ‖c‖ ≤ 6 := by
      rw [hc]
      have hsq : ‖(2 : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 = 4 + t ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have ht25 : t ^ 2 ≤ 25 := by nlinarith [abs_nonneg t, abs_le.mp ht5]
      nlinarith [hsq, norm_nonneg ((2 : ℂ) + Complex.I * (t : ℂ))]
    have hz10 : ‖z‖ ≤ 10 := by
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ 5 / 2 + 6 := by rw [hz]; linarith
        _ ≤ 10 := by norm_num
    have hb := hB0 z hz10
    have hX : (1 : ℝ) ≤ (|t| + 9) ^ 5 :=
      one_le_pow₀ (by linarith [abs_nonneg t])
    calc ‖riemannZeta₁ z‖ ≤ B0 := hb
      _ ≤ K := le_max_left _ _
      _ = K * 1 := by ring
      _ ≤ K * (|t| + 9) ^ 5 :=
          mul_le_mul_of_nonneg_left hX (le_trans (by norm_num : (0 : ℝ) ≤ 1) hKge1)
  · -- far case: `5 < |t|`
    have ht5' : (5 : ℝ) < |t| := lt_of_not_ge ht5
    have hre : |z.re - 2| ≤ 5 / 2 := by
      have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
      rw [hz] at h1
      simpa [hc] using h1
    have him : |z.im - t| ≤ 5 / 2 := by
      have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm (z - c)
      rw [hz] at h1
      simpa [hc] using h1
    have hre_lo : -(1 : ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
    have him1 : (1 : ℝ) ≤ |z.im| := by
      have h1 : |t| - |z.im| ≤ |t - z.im| := abs_sub_abs_le_abs_sub t z.im
      have h2 : |t - z.im| = |z.im - t| := abs_sub_comm _ _
      linarith
    have hz1ne : z ≠ 1 := by
      intro h1; rw [h1] at him1; simp at him1; linarith
    have hz1eq : riemannZeta₁ z = (z - 1) * riemannZeta z := zeta1_eq_mul_of_ne_one z hz1ne
    have hgle : |z.im| + 3 ≤ |t| + 9 := by
      have h2 : |z.im| ≤ |t| + 5 / 2 := by
        have h := abs_add_le (z.im - t) t
        rw [show z.im - t + t = z.im by ring] at h
        linarith
      linarith
    have hzeta : ‖riemannZeta z‖ ≤ K1 * (|t| + 9) ^ 4 := by
      by_cases h3 : z.re ≤ 3
      · have hb := hCpg z.re z.im hre_lo h3 him1
        have hze : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
          apply Complex.ext <;> simp
        rw [hze] at hb
        have h4 : (|z.im| + 3) ^ 4 ≤ (|t| + 9) ^ 4 :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |z.im| + 3) hgle 4
        calc ‖riemannZeta z‖ ≤ Cpg * (|z.im| + 3) ^ 4 := hb
          _ ≤ K1 * (|z.im| + 3) ^ 4 :=
              mul_le_mul_of_nonneg_right hCpgK1 (by positivity : (0 : ℝ) ≤ (|z.im| + 3) ^ 4)
          _ ≤ K1 * (|t| + 9) ^ 4 := mul_le_mul_of_nonneg_left h4 (le_of_lt hK1pos)
      · have h3' : 3 ≤ z.re := le_of_lt (lt_of_not_ge h3)
        have hb := hC3 z h3'
        have h4 : (1 : ℝ) ≤ (|t| + 9) ^ 4 := one_le_pow₀ (by linarith [abs_nonneg t])
        calc ‖riemannZeta z‖ ≤ C3 := hb
          _ ≤ K1 := hC3K1
          _ = K1 * 1 := by ring
          _ ≤ K1 * (|t| + 9) ^ 4 := mul_le_mul_of_nonneg_left h4 (le_of_lt hK1pos)
    have hc1 : ‖c - 1‖ ≤ |t| + 1 := by
      rw [hc]
      have hzz : (2 : ℂ) + Complex.I * (t : ℂ) - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by ring
      rw [hzz]
      calc ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
        _ = |t| + 1 := by
            rw [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
            ring
    have hnorm : ‖z - 1‖ ≤ |t| + 5 := by
      have h1 : ‖z - 1‖ ≤ ‖z - c‖ + ‖c - 1‖ := by
        have hzz : z - 1 = (z - c) + (c - 1) := by ring
        rw [hzz]; exact norm_add_le _ _
      rw [hz] at h1
      linarith
    have hgle5 : (|t| + 5) * (|t| + 9) ^ 4 ≤ (|t| + 9) ^ 5 := by
      calc (|t| + 5) * (|t| + 9) ^ 4 ≤ (|t| + 9) * (|t| + 9) ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) (by positivity)
        _ = (|t| + 9) ^ 5 := by ring
    calc ‖riemannZeta₁ z‖ = ‖(z - 1) * riemannZeta z‖ := by rw [hz1eq]
      _ = ‖z - 1‖ * ‖riemannZeta z‖ := norm_mul _ _
      _ ≤ (|t| + 5) * (K1 * (|t| + 9) ^ 4) :=
          mul_le_mul hnorm hzeta (norm_nonneg _) (by positivity)
      _ = K1 * ((|t| + 5) * (|t| + 9) ^ 4) := by ring
      _ ≤ K1 * (|t| + 9) ^ 5 := mul_le_mul_of_nonneg_left hgle5 (le_of_lt hK1pos)
      _ ≤ K * (|t| + 9) ^ 5 := mul_le_mul_of_nonneg_right hKle1 (by positivity)

end Work.LinnikAreas.DhExplicit
