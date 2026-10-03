import Mathlib
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.PinLogDev.anchor_walk
import Submission.Work.Pert.Ksub2.Setup

/-!
# `Work.Pert.PinLogDev.wc_margA_anchor_ge`

The `A`-margin of the anchor point `Xc d (-M)` of the datum's curve, at the far end `u = -M`,
is at least `M` up to an explicit `O(log M)` loss.

* `Work.Pert.margA Ξ α z = z.re - Ξ + (1/α).re + |z.im + (1/α).im|` (the `A`-margin of the gate,
  a `√2`-signed distance to the cone with apex `Ξ - 1/α`).
* `hasym` is the datum's asymptotic expansion `Xc d (-x) = -x + a log x + b + O(1/1024)`;
* `InF1 α` (`|Im α| < Re α`) makes `(1/α).re > 0` and `‖1/α‖ ≤ (1/α).re + |(1/α).im|`;
* `‖α‖ M ≤ 1/2` makes `2M ≤ ‖1/α‖`.

Hence `margA Ξ α (Xc d (-M)) ≥ M - ((|a.re|+|a.im|) log M + |b.re|+|b.im| + Ξ + 2/1024)`, which
is stronger than the stated bound by the nonnegative quantity
`(|a.re|+|a.im|) log M + 2(|a.re|+|a.im|) π + 4 - 1/512`.
-/

namespace Work.Pert.PinLogDev

/-- If `0 ≤ z.re` then `‖z‖ ≤ z.re + |z.im|` (the elementary comparison of the two norms on
`ℝ²`). -/
lemma norm_le_re_add_abs_im (z : ℂ) (hz : 0 ≤ z.re) : ‖z‖ ≤ z.re + |z.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hz] at h
  exact h

theorem wc_margA_anchor_ge {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R Ξ : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {α : ℂ} {M : ℝ} (hRM : R ≤ M) (hexp : Real.exp Real.pi ≤ M)
    (hInF1 : MandelDim.InF1 α) (hαM : ‖α‖ * M ≤ 1 / 2) :
    M - (2 * (|a.re| + |a.im|) * Real.log M
          + (2 * (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 4))
      ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) := by
  -- `M` is large, hence `log M ≥ 0`
  have hMpos : 0 < M := lt_of_lt_of_le (Real.exp_pos Real.pi) hexp
  have hM1 : 1 ≤ M := le_trans (Real.one_le_exp Real.pi_pos.le) hexp
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  -- `InF1 α` gives `Re α > 0`, hence `Re (1/α) > 0` and `‖1/α‖ ≤ Re (1/α) + |Im (1/α)|`
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hαre
    simp at hαre
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hnsq : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have hinvre : 0 ≤ (1 / α).re := by
    rw [one_div, Complex.inv_re]
    exact (div_pos hαre hnsq).le
  have hMd : 2 * M ≤ ‖(1 / α : ℂ)‖ := by
    rw [norm_div, norm_one, le_div_iff₀ hαpos]
    linarith [hαM]
  have hsum : 2 * M ≤ (1 / α).re + |(1 / α).im| :=
    le_trans hMd (norm_le_re_add_abs_im (1 / α) hinvre)
  -- the asymptotic model point
  set z : ℂ := Work.Pert.Xc d (-(M : ℂ)) with hz
  set w : ℂ := -(M : ℂ) + a * Complex.log (M : ℂ) + b with hw
  have hlogC : Complex.log (M : ℂ) = ((Real.log M : ℝ) : ℂ) :=
    (Complex.ofReal_log hMpos.le).symm
  have hwr : w.re = -M + a.re * Real.log M + b.re := by
    simp only [hw, hlogC, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hwi : w.im = a.im * Real.log M + b.im := by
    simp only [hw, hlogC, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      neg_zero]
  have hnorm : ‖z - w‖ ≤ 1 / 1024 := by rw [hz]; exact hasym M hRM
  -- real and imaginary parts of the anchor
  have hzre : -M + a.re * Real.log M + b.re - 1 / 1024 ≤ z.re := by
    have h1 : |(z - w).re| ≤ 1 / 1024 := by
      have := Complex.abs_re_le_norm (z - w)
      linarith
    rw [Complex.sub_re, hwr] at h1
    have := abs_le.mp h1
    linarith
  have hzim : |z.im| ≤ 1 / 1024 + (|a.im| * Real.log M + |b.im|) := by
    have h1 : |z.im - (a.im * Real.log M + b.im)| ≤ 1 / 1024 := by
      have h0 : |(z - w).im| ≤ 1 / 1024 := by
        have := Complex.abs_im_le_norm (z - w)
        linarith
      rw [Complex.sub_im, hwi] at h0
      exact h0
    have h2 : |a.im * Real.log M + b.im| ≤ |a.im| * Real.log M + |b.im| := by
      have h3 := abs_add_le (a.im * Real.log M) b.im
      rwa [abs_mul, abs_of_nonneg hlogM] at h3
    calc |z.im| = |(z.im - (a.im * Real.log M + b.im)) + (a.im * Real.log M + b.im)| := by
          rw [sub_add_cancel]
      _ ≤ |z.im - (a.im * Real.log M + b.im)| + |a.im * Real.log M + b.im| := abs_add_le _ _
      _ ≤ 1 / 1024 + (|a.im| * Real.log M + |b.im|) := by linarith [h1, h2]
  have himg : |(1 / α).im| - |z.im| ≤ |z.im + (1 / α).im| := by
    have h := abs_sub_abs_le_abs_sub (-(1 / α).im) z.im
    rw [abs_neg] at h
    have h2 : -(1 / α).im - z.im = -(z.im + (1 / α).im) := by ring
    rw [h2, abs_neg] at h
    exact h
  -- the two estimates add up
  have hbound : M - ((|a.re| + |a.im|) * Real.log M + |b.re| + |b.im| + Ξ + 2 * (1 / 1024))
      ≤ Work.Pert.margA Ξ α z := by
    have hAR2 : -(|a.re| * Real.log M) ≤ a.re * Real.log M := by
      have h := mul_le_mul_of_nonneg_right (neg_abs_le a.re) hlogM
      have e : -|a.re| * Real.log M = -(|a.re| * Real.log M) := by ring
      rw [e] at h
      exact h
    have hexpand : (|a.re| + |a.im|) * Real.log M
        = |a.re| * Real.log M + |a.im| * Real.log M := by ring
    unfold Work.Pert.margA
    have h1 : -M + a.re * Real.log M + b.re - 1 / 1024 - Ξ
          + ((1 / α).re + (|(1 / α).im| - |z.im|))
        ≤ z.re - Ξ + ((1 / α).re + |z.im + (1 / α).im|) := by linarith [hzre, himg]
    have h2 : M - ((|a.re| + |a.im|) * Real.log M + |b.re| + |b.im| + Ξ + 2 * (1 / 1024))
        ≤ -M + a.re * Real.log M + b.re - 1 / 1024 - Ξ
          + (2 * M - (1 / 1024 + (|a.im| * Real.log M + |b.im|))) := by
      rw [hexpand]
      linarith [hsum, hzim, hAR2, neg_abs_le b.re]
    linarith
  have hfin : M - (2 * (|a.re| + |a.im|) * Real.log M
        + (2 * (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 4))
      ≤ M - ((|a.re| + |a.im|) * Real.log M + |b.re| + |b.im| + Ξ + 2 * (1 / 1024)) := by
    have hK : 0 ≤ |a.re| + |a.im| := by positivity
    have hprod : 0 ≤ (|a.re| + |a.im|) * Real.log M := mul_nonneg hK hlogM
    have hpi : 0 ≤ (|a.re| + |a.im|) * Real.pi := mul_nonneg hK Real.pi_pos.le
    have e1 : 2 * (|a.re| + |a.im|) * Real.log M
        = 2 * ((|a.re| + |a.im|) * Real.log M) := by ring
    have e2 : 2 * (|a.re| + |a.im|) * Real.pi
        = 2 * ((|a.re| + |a.im|) * Real.pi) := by ring
    linarith
  exact le_trans hfin hbound

end Work.Pert.PinLogDev
