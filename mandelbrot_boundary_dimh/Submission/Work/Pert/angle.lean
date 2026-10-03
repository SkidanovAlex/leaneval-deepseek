import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

open Complex

/-- Elementary geometry of `Complex.arg`: if `x` has negative real part and its imaginary part is
bounded in modulus by `√3 · (−Re x)`, then `x` lies outside the open sector `{|arg| < 2π/3}`.

`Re x < 0` gives `x ≠ 0`, and `|arg x| ∈ (π/2, π]`; the hypothesis is equivalent to
`cos (arg x) > -1/2`, and `Real.cos_arg` turns that into `x.re / ‖x‖ > -1/2`, i.e.
`2 * (-x.re) < ‖x‖`.  Squaring (`Complex.sq_norm`, `Complex.normSq_apply`) gives
`3 * x.re ^ 2 < x.im ^ 2`, i.e. `√3 * (-x.re) < |x.im|`, contradicting the hypothesis. -/
theorem angleArg {x : ℂ} (hre : x.re < 0) (him : |x.im| < Real.sqrt 3 * (-x.re)) :
    2 * Real.pi / 3 ≤ |Complex.arg x| := by
  by_contra hcon
  push Not at hcon
  have hx0 : x ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hcos23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hcos : -1 / 2 < Real.cos (Complex.arg x) := by
    have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := |Complex.arg x|) (y := 2 * Real.pi / 3)
      (abs_nonneg _) (by linarith [Real.pi_pos]) hcon
    rw [Real.cos_abs, hcos23] at h1
    linarith
  rw [Complex.cos_arg hx0] at hcos
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hA : (-1 / 2) * ‖x‖ < x.re := (lt_div_iff₀ hn).mp hcos
  have h2 : 2 * (-x.re) < ‖x‖ := by linarith
  have hpos : 0 < -x.re := by linarith
  have h4 : (2 * (-x.re)) ^ 2 < ‖x‖ ^ 2 := by nlinarith [h2, hpos]
  rw [Complex.sq_norm, Complex.normSq_apply] at h4
  have h5 : Real.sqrt 3 * (-x.re) < |x.im| := by
    have h6 : 3 * x.re ^ 2 < x.im ^ 2 := by nlinarith [h4]
    have h7 : (Real.sqrt 3 * (-x.re)) ^ 2 < x.im ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith [h6]
    have h8 : |Real.sqrt 3 * (-x.re)| < |x.im| := sq_lt_sq.mp h7
    rwa [abs_of_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hpos)] at h8
  exact absurd him (not_lt.mpr h5.le)

/-- Sector algebra: for `α` in the open sector `|arg α| < π/4` (written `|Im α| < Re α`) and a
real `μ ≥ 1/2`, the point `w = −μ/α` lies in the left sector, with `Re w < 0`, `|Im w| ≤ −Re w`,
`‖w‖ = μ/‖α‖`, and `‖w‖ ≤ (3/2)(−Re w)` (since `−Re w = μ Re α/‖α‖²` and
`‖α‖ ≤ √2 Re α < (3/2) Re α`). -/
theorem sectorShift {α : ℂ} (hα : |α.im| < α.re) {μ : ℝ} (hμ : 1 / 2 ≤ μ) (w : ℂ)
    (hw : w = -(μ : ℂ) / α) :
    w.re < 0 ∧ |w.im| ≤ -w.re ∧ ‖w‖ = μ / ‖α‖ ∧ ‖w‖ ≤ 3 / 2 * (-w.re) := by
  have hμpos : 0 < μ := by linarith
  have ha : 0 < α.re := by have := abs_nonneg α.im; linarith
  have hα0 : α ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hns : 0 < Complex.normSq α := by rw [Complex.normSq_eq_norm_sq]; positivity
  have hwmul : w = -(μ : ℂ) * α⁻¹ := by rw [hw, div_eq_mul_inv]
  have hre : w.re = -μ * α.re / Complex.normSq α := by
    rw [hwmul, Complex.mul_re, Complex.inv_re, Complex.inv_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : w.im = μ * α.im / Complex.normSq α := by
    rw [hwmul, Complex.mul_im, Complex.inv_re, Complex.inv_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnorm : ‖w‖ = μ / ‖α‖ := by
    rw [hwmul, norm_mul, norm_neg, norm_inv]
    simp [abs_of_pos hμpos, div_eq_mul_inv]
  have hnα : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  refine ⟨?_, ?_, hnorm, ?_⟩
  · rw [hre]
    exact div_neg_of_neg_of_pos (by nlinarith) hns
  · have h1 : |μ * α.im| ≤ μ * α.re := by
      rw [abs_mul, abs_of_pos hμpos]
      exact mul_le_mul_of_nonneg_left hα.le hμpos.le
    rw [him, hre]
    rw [show -( -μ * α.re / Complex.normSq α) = μ * α.re / Complex.normSq α by ring]
    rw [abs_div, abs_of_pos hns]
    exact div_le_div_of_nonneg_right h1 hns.le
  · have hb : α.im ^ 2 ≤ α.re ^ 2 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp hα
      nlinarith
    have hs : ‖α‖ ≤ 3 / 2 * α.re := by
      have hsq : ‖α‖ ^ 2 ≤ (3 / 2 * α.re) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith [hb, ha]
      calc ‖α‖ = Real.sqrt (‖α‖ ^ 2) := (Real.sqrt_sq (norm_nonneg α)).symm
        _ ≤ Real.sqrt ((3 / 2 * α.re) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 3 / 2 * α.re := Real.sqrt_sq (by linarith)
    rw [hnorm, hre]
    rw [show -( -μ * α.re / Complex.normSq α) = μ * α.re / Complex.normSq α by ring]
    rw [Complex.normSq_eq_norm_sq, div_le_iff₀ hnα]
    rw [show 3 / 2 * (μ * α.re / ‖α‖ ^ 2) * ‖α‖ = 3 / 2 * μ * α.re / ‖α‖ by
      field_simp]
    rw [le_div_iff₀ hnα]
    nlinarith [hs, hμpos]

/-- **(A.4.5′)**: the angle condition of (4.2.3) forces the exponent `k = n` to be positive.  Here
`x = n + e - (m - 1/2)/α`: `n` is the (tentative) integer exponent, `m ≥ 1` the number of iterates
of the return map, `α ∈ 𝓕₁` (`MandelDim.InF1 α`) the rotation number and `e` the accumulated error
of the return map, bounded by `m/(8|α|)` in Shishikura's normalization.  Since
`arg (-(m - 1/2)/α) ∈ (3π/4, 5π/4)` and `n ≤ 0` keeps the sum in that sector, `x` can only enter
`{|arg| < 2π/3}` if `n ≥ 1`. -/
theorem angle {α : ℂ} (hF1 : MandelDim.InF1 α) {e : ℂ} {m : ℕ} (hm : 1 ≤ m) {k : ℤ}
    (he : ‖e‖ < (m : ℝ) / (20 * ‖α‖))
    (x : ℂ) (hx : x = (k : ℂ) + e - ((m : ℂ) - 1 / 2) / α)
    (harg : |Complex.arg x| < 2 * Real.pi / 3) :
    1 ≤ k := by
  by_contra hk
  push Not at hk
  have hk0 : k ≤ 0 := by omega
  have hF1' : |α.im| < α.re := hF1
  set μ : ℝ := (m : ℝ) - 1 / 2 with hμdef
  have hμ : 1 / 2 ≤ μ := by
    rw [hμdef]
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcast : ((m : ℂ) - 1 / 2) = (μ : ℂ) := by
    rw [hμdef]
    push_cast
    ring
  have hx' : x = (k : ℂ) + e - (μ : ℂ) / α := by rw [hx, hcast]
  set w : ℂ := -(μ : ℂ) / α with hwdef
  have hxw : x = (k : ℂ) + e + w := by rw [hx', hwdef]; ring
  obtain ⟨hwre, hwim, hwnorm, hwbound⟩ := sectorShift hF1' hμ w hwdef
  have hα0 : α ≠ 0 := by intro h; rw [h] at hF1'; simp at hF1'
  have hnormα : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hβ : 0 < -w.re := by linarith
  -- the accumulated error is at most `3/20` of `-Re w`
  have hc : ‖e‖ < 3 / 20 * (-w.re) := by
    have hm2 : (m : ℝ) ≤ 2 * μ := by rw [hμdef]; linarith
    have h1 : (m : ℝ) / (20 * ‖α‖) ≤ μ / (10 * ‖α‖) := by
      have h2 : (m : ℝ) / (20 * ‖α‖) ≤ (2 * μ) / (20 * ‖α‖) :=
        div_le_div_of_nonneg_right hm2 (by positivity)
      have h3 : (2 * μ) / (20 * ‖α‖) = μ / (10 * ‖α‖) := by ring
      rwa [h3] at h2
    have h4 : μ / (10 * ‖α‖) ≤ 3 / 20 * (-w.re) := by
      have hb := hwbound
      rw [hwnorm] at hb
      have h5 : μ / (10 * ‖α‖) = 1 / 10 * (μ / ‖α‖) := by ring
      rw [h5]
      linarith
    linarith
  have hxre : x.re = (k : ℝ) + e.re + w.re := by
    rw [hxw]
    simp
  have hxre_le : x.re ≤ ‖e‖ + w.re := by
    rw [hxre]
    have hk0' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have he_re : e.re ≤ ‖e‖ := by
      have h := Complex.abs_re_le_norm e
      rw [abs_le] at h
      linarith [h.2]
    linarith
  have hre_neg : x.re < 0 := by linarith [hxre_le, hc, hwre]
  have hxim : x.im = e.im + w.im := by
    rw [hxw]
    simp
  have him_bound : |x.im| < Real.sqrt 3 * (-x.re) := by
    have he_im : |e.im| ≤ ‖e‖ := Complex.abs_im_le_norm e
    have h1 : |x.im| ≤ ‖e‖ + (-w.re) := by
      rw [hxim]
      calc |e.im + w.im| ≤ |e.im| + |w.im| := abs_add_le _ _
        _ ≤ ‖e‖ + (-w.re) := by linarith [he_im, hwim]
    have hA : (17 / 20) * (-w.re) < -x.re := by linarith [hxre_le, hc]
    have hB : |x.im| < (23 / 20) * (-w.re) := by linarith [h1, hc]
    have hs3 : (8 : ℝ) / 5 < Real.sqrt 3 :=
      (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 5)).mpr (by norm_num)
    have hC : (23 / 20) * (-w.re) ≤ Real.sqrt 3 * ((17 / 20) * (-w.re)) := by
      have h23 : (23 : ℝ) / 20 ≤ Real.sqrt 3 * (17 / 20) := by nlinarith [hs3]
      nlinarith [h23, hβ]
    have hD : Real.sqrt 3 * ((17 / 20) * (-w.re)) < Real.sqrt 3 * (-x.re) :=
      mul_lt_mul_of_pos_left hA (Real.sqrt_pos.mpr (by norm_num))
    linarith
  exact absurd (angleArg hre_neg him_bound) (not_le.mpr harg)

end Work.Pert
