/-
# Elementary geometry of the cusp-`0` tile `E = KEpsilon` and the two-regime window

The cusp-`0` tile `E = KEpsilon = {w ∈ 𝒟 : 2 ≤ Im (S • w)}` (`Submission/Work/Asymptotics/KEpsilon.lean`)
is the region on which the polynomial-window bound `Work.Asymptotics.EPolyWindowE_one` is stated.
This file collects the elementary geometric facts about it:

* `E_im_le_half`, `E_norm_le_half` : `Im w ≤ 1/2`, `‖w‖ ≤ 1/2` on `E`;
* `E_re_sq_lt` : `(Re w)² < ‖w‖⁴`, the `𝒟`-conditions `‖w ∓ 1/2‖ > 1/2`;
* `E_scale_le_im_S_add_two` : the key comparison `scale w ≤ Im (S • w) + 2`; since the poles
  of `z ↦ K(w,z)` lie on the orbit of `w`, the highest one is `z = S • w` of height `Im (S • w)`,
  so this says `scale w` is the pole height up to an additive constant.  It is exactly what turns
  the exponential factor `e^{2πt}` of the (`d = 24`) kernel into a bounded factor for `t ≤ scale w`;
* `E_S_im_ge` : `3/2 ≤ Im (S • w)` (the form in which the `E`-estimates
  `Work.Asymptotics.Xi8_bound_E` / `Xi24_bound_E` consume the tile).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

lemma E_S_im (w : UpperHalfPlane) :
    (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
  rw [Work.Kernels.im_smul_eq, Work.Kernels.jFun_apply]
  simp

lemma E_normSq_eq (w : UpperHalfPlane) :
    ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

lemma E_norm_pos (w : UpperHalfPlane) : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero

lemma E_im_le_norm (w : UpperHalfPlane) : w.im ≤ ‖(w : ℂ)‖ := by
  have h1 := Complex.abs_im_le_norm (w : ℂ)
  rw [UpperHalfPlane.coe_im, abs_of_pos w.im_pos] at h1
  exact h1

private lemma E_two_normSq_le_im {w : UpperHalfPlane} (hw : w ∈ KEpsilon) :
    2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := by
  have hS : 2 ≤ (ModularGroup.S • w).im := hw.2
  rw [E_S_im] at hS
  have hn : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos (E_norm_pos w) 2
  rw [le_div_iff₀ hn] at hS
  linarith [hS]

/-- On `E`, `Im w ≤ 1/2` and `‖w‖ ≤ 1/2`. -/
lemma E_im_le_half {w : UpperHalfPlane} (hw : w ∈ KEpsilon) : w.im ≤ 1 / 2 := by
  have h2 := E_two_normSq_le_im hw
  have h3 : 2 * (w.im) ^ 2 ≤ 2 * ‖(w : ℂ)‖ ^ 2 := by
    have := E_normSq_eq w
    nlinarith [sq_nonneg w.re]
  nlinarith [le_trans h3 h2, w.im_pos]

/-- On `E`, `‖w‖ ≤ 1/2`. -/
lemma E_norm_le_half {w : UpperHalfPlane} (hw : w ∈ KEpsilon) : ‖(w : ℂ)‖ ≤ 1 / 2 := by
  have h2 := E_two_normSq_le_im hw
  have h3 : w.im ≤ ‖(w : ℂ)‖ := E_im_le_norm w
  have h4 : 2 * ‖(w : ℂ)‖ ^ 2 ≤ ‖(w : ℂ)‖ := le_trans h2 h3
  have h5 : 0 < ‖(w : ℂ)‖ := E_norm_pos w
  have h6 : 2 * ‖(w : ℂ)‖ ≤ 1 := by
    have h7 : (2 * ‖(w : ℂ)‖) * ‖(w : ℂ)‖ ≤ 1 * ‖(w : ℂ)‖ := by
      rw [one_mul]
      calc (2 * ‖(w : ℂ)‖) * ‖(w : ℂ)‖ = 2 * ‖(w : ℂ)‖ ^ 2 := by ring
        _ ≤ ‖(w : ℂ)‖ := h4
    exact le_of_mul_le_mul_right h7 h5
  linarith

/-- On `E`, `(Re w)² < ‖w‖⁴`: this is the `𝒟`-condition `|Re w| < ‖w‖²`, which is equivalent
to `‖w ∓ 1/2‖ > 1/2`. -/
lemma E_re_sq_lt {w : UpperHalfPlane} (hw : w ∈ KEpsilon) : w.re ^ 2 < ‖(w : ℂ)‖ ^ 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := (mem_DomainD).mp hw.1
  have h3' : (1 / 2 : ℝ) ^ 2 < ‖(w : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg ((w : ℂ) - (1 / 2 : ℂ))]
  have h4' : (1 / 2 : ℝ) ^ 2 < ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg ((w : ℂ) + (1 / 2 : ℂ))]
  have e3 : ‖(w : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (w.re - 1 / 2) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e4 : ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (w.re + 1 / 2) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hs : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := E_normSq_eq w
  rw [e3] at h3'
  rw [e4] at h4'
  have habs : |w.re| < ‖(w : ℂ)‖ ^ 2 := by
    rw [abs_lt]
    constructor <;> nlinarith
  nlinarith [sq_abs w.re, habs, abs_nonneg w.re]

/-- **The key geometry of the tile**: on `E`, `scale w ≤ Im (S • w) + 2`.  Since the highest
pole of `z ↦ K(w,z)` is at `z = S • w`, this is the statement that `scale w` is (up to an
additive constant) the pole height, i.e. the threshold of the window `t ≤ scale w`. -/
lemma E_scale_le_im_S_add_two {w : UpperHalfPlane} (hw : w ∈ KEpsilon) :
    Work.Kernels.scale w ≤ (ModularGroup.S • w).im + 2 := by
  have hre := E_re_sq_lt hw
  have hn := E_norm_pos w
  have hn2 : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos hn 2
  have hsq := E_normSq_eq w
  have hS := E_S_im w
  have hnorm : ‖(w : ℂ)‖ ≤ 1 / 2 := E_norm_le_half hw
  have hkey : (w.im)⁻¹ - w.im / ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 / (w.im * ‖(w : ℂ)‖ ^ 2) := by
    rw [inv_eq_one_div, div_sub_div _ _ (ne_of_gt w.im_pos) (ne_of_gt hn2)]
    congr 1
    rw [hsq]
    ring
  have h2n : 2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := E_two_normSq_le_im hw
  have hlt : w.re ^ 2 / (w.im * ‖(w : ℂ)‖ ^ 2) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hre, hnorm, w.im_pos, hn, h2n]
  rw [Work.Kernels.scale, hS]
  have : (w.im)⁻¹ = w.re ^ 2 / (w.im * ‖(w : ℂ)‖ ^ 2) + w.im / ‖(w : ℂ)‖ ^ 2 := by
    linarith [hkey]
  rw [this]
  linarith

/-- On `E` the `S`-image has imaginary part at least `3/2`. -/
lemma E_S_im_ge (w : UpperHalfPlane) (hw : w ∈ KEpsilon) :
    (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im := le_trans (by norm_num) hw.2

end Work.Asymptotics
