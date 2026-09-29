import Mathlib
import Submission.Work.CNum.Jfun_defs

/-! # CNum: the geometric bounds on the arc `ψ ∈ (-3.905, -2.385)`

This file proves the two numerical facts about the circle point
`w ψ = c₂ + ρ₂ e^{iψ}` (with `cJ = 629/572`, `uJ = 115/143`) that the chord
argument for `Jfun` needs on the arc `ψ ∈ (-3.905, -2.385)`:

* `Real.cos ψ ≤ -7/10`, and
* `‖w ψ‖ ≤ rJ = 79/100`.

Both are elementary.  Writing `ψ = t - π` with `t = ψ + π`, we have
`cos ψ = -cos t` and `|t| < 0.763408`, so `t ^ 2 < 3/5` and the quadratic lower
bound `1 - x^2/2 ≤ cos x` gives `cos t > 7/10`.  For the norm, `‖w ψ‖²` equals the
quadratic form `KK ψ = c₂² + ρ₂² + 2 c₂ ρ₂ cos ψ`, which is maximised at the smallest
possible `cos ψ = -7/10`; the resulting rational value is `< (79/100)²`. -/

namespace Work.CNum

open Complex

/-- The real part of the circle point `w ψ`. -/
private lemma wf_re_arc (ψ : ℝ) : (wf ψ).re = cJ + uJ * Real.cos ψ := by
  have hexp : Complex.exp (Complex.I * ψ) = (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I := by
    rw [show Complex.I * ψ = ψ * Complex.I from by ring]
    exact Complex.exp_ofReal_mul_I ψ
  rw [wf, hexp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the circle point `w ψ`. -/
private lemma wf_im_arc (ψ : ℝ) : (wf ψ).im = uJ * Real.sin ψ := by
  have hexp : Complex.exp (Complex.I * ψ) = (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I := by
    rw [show Complex.I * ψ = ψ * Complex.I from by ring]
    exact Complex.exp_ofReal_mul_I ψ
  rw [wf, hexp]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- `‖w ψ‖²` is the quadratic form `KK ψ`. -/
private lemma norm_wf_sq_arc (ψ : ℝ) : ‖wf ψ‖ ^ 2 = KK ψ := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, KK, wf_re_arc, wf_im_arc]
  nlinarith [Real.sin_sq_add_cos_sq ψ]

theorem arc_bounds {ψ : ℝ} (hψ : ψ ∈ Set.Ioo (-3.905) (-2.385)) : Real.cos ψ ≤ -7/10 ∧ ‖wf ψ‖ ≤ rJ := by
  obtain ⟨h1, h2⟩ := hψ
  -- write `ψ = t - π`, `t = ψ + π`, with `|t| < 0.763408`
  have habs : |ψ + Real.pi| < (0.763408 : ℝ) := by
    have h1' : (-0.763408 : ℝ) < ψ + Real.pi := by linarith [Real.pi_gt_d6]
    have h2' : ψ + Real.pi < (0.763408 : ℝ) := by linarith [Real.pi_lt_d6]
    exact abs_lt.mpr ⟨h1', h2'⟩
  have ht2 : (ψ + Real.pi) ^ 2 < (3 / 5 : ℝ) := by
    have hs : (ψ + Real.pi) ^ 2 < (0.763408 : ℝ) ^ 2 := by
      rw [sq_lt_sq]
      rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.763408)]
    have h763 : (0.763408 : ℝ) ^ 2 < (3 / 5 : ℝ) := by norm_num
    linarith
  -- the quadratic lower bound for cosine
  have hcos_low : (7 / 10 : ℝ) < Real.cos (ψ + Real.pi) := by
    have := Real.one_sub_sq_div_two_le_cos (x := ψ + Real.pi)
    nlinarith
  have hcos : Real.cos ψ ≤ -7/10 := by
    have e : Real.cos ψ = -Real.cos (ψ + Real.pi) := by
      have h := Real.cos_sub_pi (ψ + Real.pi)
      rw [add_sub_cancel_right] at h
      exact h
    rw [e]; linarith
  -- the norm bound
  have hKK : KK ψ ≤ (79 / 100 : ℝ) ^ 2 := by
    have h2cu : (0 : ℝ) ≤ 2 * cJ * uJ := by unfold cJ uJ; norm_num
    have key : 2 * cJ * uJ * Real.cos ψ ≤ 2 * cJ * uJ * (-7/10) :=
      mul_le_mul_of_nonneg_left hcos h2cu
    have hcalc : cJ ^ 2 + uJ ^ 2 + 2 * cJ * uJ * (-7/10) ≤ (79 / 100 : ℝ) ^ 2 := by
      unfold cJ uJ; norm_num
    rw [KK]; linarith
  refine ⟨hcos, ?_⟩
  have hle : ‖wf ψ‖ ≤ 79 / 100 := by
    have hsq : ‖wf ψ‖ ^ 2 ≤ (79 / 100 : ℝ) ^ 2 := by
      rw [norm_wf_sq_arc]; exact hKK
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 79 / 100)] at this
  simpa only [rJ] using hle

end Work.CNum
