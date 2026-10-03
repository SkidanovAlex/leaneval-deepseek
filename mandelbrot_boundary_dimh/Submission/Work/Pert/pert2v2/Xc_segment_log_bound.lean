import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.pert2v2

/-- Principal-branch estimate for the complex logarithm: `‖log z‖ ≤ |log ‖z‖| + π`.

`log_re`/`log_im` identify the real and imaginary parts of `Complex.log z` with `Real.log ‖z‖`
and `Complex.arg z`, the general bound `‖ζ‖ ≤ |ζ.re| + |ζ.im|` gives the first term, and
`|arg z| ≤ π` the second. -/
theorem norm_log_le_abs_log_norm_add_pi (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  refine (Complex.norm_le_abs_re_add_abs_im (Complex.log z)).trans ?_
  rw [Complex.log_re, Complex.log_im]
  have h := Complex.abs_arg_le_pi z
  linarith

/-- **The curve `Xc d = τ₀ ∘ d.φ` is a bounded logarithmic perturbation of the identity on the
segment `{x + i y₀ : x ∈ [0,1)}`.**  Direct corollary of the datum's asymptotic
`ParabData.φ_asymp` (`tau0 (d.φ w) = w + a log(-w) + b + o(1)` on the sector `QLeft ξ₀`, which
contains `x + i y₀` for `y₀` large since its argument tends to `π/2 > π/3`), with the principal
branch estimate `‖log (-u)‖ ≤ log ‖u‖ + π`.

This is the localisation of `Xc d w` at the segment which the `(RIG)`-based `hres` row needs: it
places `Xc d (x + i y₀)` in the same height-`≈ y₀` region as the gate preimage `ς` of `x + i y₀`
(with `|Re| ≤ 1 + A log(y₀+2) + C`), so that the segment `[ς, Xc d w]` lies inside the gate at high
height and the mean-value/modulus arguments apply. -/
theorem Xc_segment_log_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ A C Y : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        - ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ ≤ A * Real.log (y₀ + 2) + C := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  -- the accuracy `1` of the asymptotic, and the resulting threshold `R`
  obtain ⟨R, hR⟩ := hasym 1 one_pos
  refine ⟨‖a‖, 1 + ‖a‖ * Real.pi + ‖b‖, max (R + 1) (max (2 * (1 + d.ξ₀)) 1),
    norm_nonneg a, ?_, ?_⟩
  · have ha := norm_nonneg a
    have hb := norm_nonneg b
    have hp : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    have hmul : 0 ≤ ‖a‖ * Real.pi := mul_nonneg ha hp
    linarith
  intro y₀ hy x hx
  obtain ⟨hx0, hx1⟩ := hx
  -- thresholds extracted from `y₀ ≥ Y`
  have hY : max (R + 1) (max (2 * (1 + d.ξ₀)) 1) ≤ y₀ := hy
  have h1 : R + 1 ≤ y₀ :=
    le_trans (le_max_left (R + 1) (max (2 * (1 + d.ξ₀)) 1)) hY
  have h2 : max (2 * (1 + d.ξ₀)) 1 ≤ y₀ :=
    le_trans (le_max_right (R + 1) (max (2 * (1 + d.ξ₀)) 1)) hY
  have hy1 : (1 : ℝ) ≤ y₀ := le_trans (le_max_right (2 * (1 + d.ξ₀)) 1) h2
  have hyξ : 2 * (1 + d.ξ₀) ≤ y₀ := le_trans (le_max_left (2 * (1 + d.ξ₀)) 1) h2
  have hyR : R < y₀ := by linarith
  have hy0 : 0 < y₀ := lt_of_lt_of_le zero_lt_one hy1
  -- the point of the segment, and its basic coordinates
  set w : ℂ := (x : ℂ) + (y₀ : ℂ) * Complex.I with hwdef
  have hwre : w.re = x := by rw [hwdef]; simp
  have hwim : w.im = y₀ := by rw [hwdef]; simp
  have hwnorm_ge : y₀ ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos hy0] at h
    exact h
  have hwnorm_le : ‖w‖ ≤ y₀ + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_nonneg hx0, abs_of_pos hy0] at h
    linarith
  have hwnorm_pos : 0 < ‖w‖ := lt_of_lt_of_le hy0 hwnorm_ge
  -- the point lies in the repelling sector `QLeft ξ₀`
  have hQ : w ∈ MandelDim.QLeft d.ξ₀ := by
    rw [Work.Parab.QLeft_iff]
    have hre : (w + (d.ξ₀ : ℂ)).re = x + d.ξ₀ := by
      rw [Complex.add_re, Complex.ofReal_re, hwre]
    have him : (w + (d.ξ₀ : ℂ)).im = y₀ := by
      rw [Complex.add_im, Complex.ofReal_im, hwim]
      ring
    rw [hre]
    calc 2 * (x + d.ξ₀) < 2 * (1 + d.ξ₀) := by linarith
      _ ≤ y₀ := hyξ
      _ = |(w + (d.ξ₀ : ℂ)).im| := by rw [him, abs_of_pos hy0]
      _ ≤ ‖w + (d.ξ₀ : ℂ)‖ := Complex.abs_im_le_norm _
  -- the asymptotic at `w`
  have hasymw : ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖ < 1 :=
    hR w hQ (lt_of_lt_of_le hyR hwnorm_ge)
  -- the principal-branch logarithm estimate at `-w`
  have hlogbound : ‖Complex.log (-w)‖ ≤ Real.log (y₀ + 2) + Real.pi := by
    have h1 := norm_log_le_abs_log_norm_add_pi (-w)
    have h2 : |Real.log ‖-w‖| ≤ Real.log (y₀ + 2) := by
      rw [norm_neg, abs_of_nonneg (Real.log_nonneg (le_trans hy1 hwnorm_ge))]
      exact Real.log_le_log hwnorm_pos hwnorm_le
    linarith
  -- the decomposition `Xc d w - w = (τ₀ (φ w) - (w + a log(-w) + b)) + (a log(-w) + b)`
  have heq : Work.Pert.Xc d w - w
      = (MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b))
        + (a * Complex.log (-w) + b) := by
    simp only [Work.Pert.Xc]
    ring
  rw [heq]
  calc ‖(MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b))
          + (a * Complex.log (-w) + b)‖
      ≤ ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖
          + ‖a * Complex.log (-w) + b‖ := norm_add_le _ _
    _ ≤ 1 + (‖a‖ * ‖Complex.log (-w)‖ + ‖b‖) := by
        have h2 : ‖a * Complex.log (-w) + b‖ ≤ ‖a‖ * ‖Complex.log (-w)‖ + ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
        linarith
    _ ≤ 1 + (‖a‖ * (Real.log (y₀ + 2) + Real.pi) + ‖b‖) := by
        have h3 := mul_le_mul_of_nonneg_left hlogbound (norm_nonneg a)
        linarith
    _ = ‖a‖ * Real.log (y₀ + 2) + (1 + ‖a‖ * Real.pi + ‖b‖) := by ring

end Work.Pert.pert2v2
