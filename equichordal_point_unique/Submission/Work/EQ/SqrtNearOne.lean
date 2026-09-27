import Mathlib

/-!
# The principal square root near `1`

Elementary facts about `z ↦ (1+z)^(1/2)` (principal branch, `Complex.cpow`) for `‖z‖ ≤ 1/2`:
it is analytic, its square is `1+z`, it commutes with complex conjugation, and it is
1-Lipschitz, `‖(1+z)^(1/2) - 1‖ ≤ ‖z‖`, with `‖(1+(1+z)^(1/2))⁻¹‖ ≤ 1`.
-/

namespace Work.EQ

open Complex Metric Filter

noncomputable section

/-- The principal square root of `1+z`, as a function of `z`. -/
noncomputable def sqHalf (z : ℂ) : ℂ := (1 + z) ^ (1 / 2 : ℂ)

lemma sqHalf_sq (z : ℂ) : sqHalf z ^ 2 = 1 + z := by
  have h : ((1 + z) ^ ((2 : ℂ))⁻¹) ^ 2 = 1 + z :=
    Complex.cpow_nat_inv_pow (1 + z) (by norm_num)
  have h2 : ((2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by norm_num
  rw [sqHalf, ← h2]
  exact h

lemma sqHalf_zero : sqHalf 0 = 1 := by
  simp only [sqHalf, add_zero]
  exact Complex.one_cpow _

lemma one_add_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 + z).re := by
  have h : (1 + z).re = 1 + z.re := by simp
  have h2 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  rw [h]
  linarith [(abs_le.mp h2).1]

lemma one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro h
  have := one_add_re_pos hz
  rw [h] at this
  simp at this

lemma sqHalf_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (sqHalf z).re := by
  have hz' : 1 + z ≠ 0 := one_add_ne_zero hz
  have hzre : 0 < (1 + z).re := one_add_re_pos hz
  rw [sqHalf, Complex.cpow_def_of_ne_zero hz', Complex.exp_re]
  have hhalf : (1 / 2 : ℂ) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by norm_num
  have hre : (Complex.log (1 + z) * (1 / 2 : ℂ)).re = (Complex.log (1 + z)).re / 2 := by
    rw [hhalf, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have him : (Complex.log (1 + z) * (1 / 2 : ℂ)).im = (Complex.log (1 + z)).im / 2 := by
    rw [hhalf, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
    ring
  rw [hre, him, Complex.log_im]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  rw [Set.mem_Ioo]
  have h1 : -(Real.pi) < (1 + z).arg := Complex.neg_pi_lt_arg _
  have h2 : (1 + z).arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
  constructor <;> linarith

lemma sqHalf_add_one_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : sqHalf z + 1 ≠ 0 := by
  intro h
  have h1 : (sqHalf z).re + 1 = 0 := by
    have := congrArg Complex.re h
    simpa using this
  have := sqHalf_re_pos hz
  linarith

lemma sqHalf_sub_one_mul (z : ℂ) : (sqHalf z - 1) * (sqHalf z + 1) = z := by
  have h := sqHalf_sq z
  linear_combination h

lemma sqHalf_sub_one {z : ℂ} (hz : ‖z‖ < 1) : sqHalf z - 1 = z / (sqHalf z + 1) := by
  rw [eq_div_iff (sqHalf_add_one_ne_zero hz)]
  exact sqHalf_sub_one_mul z

lemma norm_sqHalf_add_one_ge_one {z : ℂ} (hz : ‖z‖ < 1) : 1 ≤ ‖sqHalf z + 1‖ := by
  have h := sqHalf_re_pos hz
  have h2 : (sqHalf z + 1).re = (sqHalf z).re + 1 := by simp
  have h3 : (sqHalf z + 1).re ≤ ‖sqHalf z + 1‖ := Complex.re_le_norm _
  rw [h2] at h3
  linarith

lemma norm_sqHalf_sub_one_le {z : ℂ} (hz : ‖z‖ < 1) : ‖sqHalf z - 1‖ ≤ ‖z‖ := by
  have hne := sqHalf_add_one_ne_zero hz
  rw [sqHalf_sub_one hz, norm_div]
  have h1 := norm_sqHalf_add_one_ge_one hz
  have hpos : (0 : ℝ) < ‖sqHalf z + 1‖ := by linarith
  rw [div_le_iff₀ hpos]
  calc ‖z‖ = ‖z‖ * 1 := (mul_one _).symm
    _ ≤ ‖z‖ * ‖sqHalf z + 1‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg z)

lemma norm_inv_sqHalf_add_one_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(sqHalf z + 1)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have h1 := norm_sqHalf_add_one_ge_one hz
  rw [inv_le_one₀ (by linarith : (0 : ℝ) < ‖sqHalf z + 1‖)]
  exact h1

lemma norm_sqHalf_sub_sqHalf_le {z w : ℂ} (hz : ‖z‖ ≤ 1 / 2) (hw : ‖w‖ ≤ 1 / 2) :
    ‖sqHalf z - sqHalf w‖ ≤ ‖z - w‖ := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hw1 : ‖w‖ < 1 := by linarith
  have hzw : (sqHalf z - sqHalf w) * (sqHalf z + sqHalf w) = z - w := by
    have h1 := sqHalf_sq z
    have h2 := sqHalf_sq w
    linear_combination h1 - h2
  have hbound : ∀ v : ℂ, ‖v‖ ≤ 1 / 2 → (1 / 2 : ℝ) ≤ (sqHalf v).re := by
    intro v hv
    have hv' : ‖v‖ < 1 := by linarith
    have h4 : |(sqHalf v).re - 1| ≤ ‖sqHalf v - 1‖ := by
      simpa using Complex.abs_re_le_norm (sqHalf v - 1)
    have h5 := norm_sqHalf_sub_one_le hv'
    have h6 : |(sqHalf v).re - 1| ≤ ‖v‖ := le_trans h4 h5
    linarith [(abs_le.mp h6).1]
  have hlow : 1 ≤ ‖sqHalf z + sqHalf w‖ := by
    have h2 : (sqHalf z + sqHalf w).re = (sqHalf z).re + (sqHalf w).re := by simp
    have h3 : (sqHalf z + sqHalf w).re ≤ ‖sqHalf z + sqHalf w‖ := Complex.re_le_norm _
    have hz2 := hbound z hz
    have hw2 := hbound w hw
    linarith
  rw [← hzw, norm_mul]
  nlinarith [norm_nonneg (sqHalf z - sqHalf w), hlow]

lemma analyticAt_sqHalf {z : ℂ} (hz : 0 < (1 + z).re) : AnalyticAt ℂ sqHalf z := by
  have hmem : (1 + z) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have h1 : AnalyticAt ℂ (fun w : ℂ => 1 + w) z := analyticAt_const.add analyticAt_id
  have h2 : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) z := analyticAt_const
  exact h1.cpow h2 hmem

lemma analyticOnNhd_sqHalf {s : Set ℂ} (hs : ∀ z ∈ s, 0 < (1 + z).re) :
    AnalyticOnNhd ℂ sqHalf s := fun z hz => analyticAt_sqHalf (hs z hz)

lemma conj_sqHalf {z : ℂ} (hz : 0 < (1 + z).re) :
    starRingEnd ℂ (sqHalf z) = sqHalf (starRingEnd ℂ z) := by
  have harg : (1 + z).arg ≠ Real.pi := by
    have h := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    intro hh
    rw [hh] at h
    linarith [Real.pi_pos]
  have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    simp only [map_div₀, map_one, map_ofNat]
  have h := Complex.cpow_conj (1 + z) (1 / 2 : ℂ) harg
  rw [hhalf] at h
  have h2 : sqHalf z = starRingEnd ℂ ((starRingEnd ℂ (1 + z)) ^ (1 / 2 : ℂ)) := by
    simpa [sqHalf] using h
  rw [h2, Complex.conj_conj]
  simp [sqHalf]

end

end Work.EQ
