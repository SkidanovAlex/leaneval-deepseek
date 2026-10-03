import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xcurve_bounds

/-!
# `Work.Pert.Ksub2.Engine`

Geometric layer for the proof of `Work.Pert.Ksub_phi_close_v2` *at a FIXED depth*.

The plan (see `Ksub2/NOTES.md`): pin the perturbed Fatou coordinate at the datum's anchor `u₀ = -M`
(so that `ρ u = Φm (Xc d u) - u` vanishes at `u₀`), and compare `Φm` with the datum's local
coordinate `Φ₀` (the local inverse of `Xc d`, which exists on a ball around `Xc d u₀`) via the
*derivative* comparison `deriv_diff_le` (Fatou's estimate applied to both near-translations) plus
the mean value inequality.  `M` is chosen once and for all from the fixed data (`K'`, `d`, `Ξ`) —
it does NOT tend to infinity — so all subsequent estimates are over fixed compacta.

This file records the elementary geometry used by that argument:

* `MemQm`: membership in the gate `Qm ξ α` from two real-part inequalities;
* `Dstrip`: the deep strip `{-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}` (already defined in `Setup.lean`);
* `Dstrip_ball_sub_Qm`: a ball of radius `≤ M/4` around a point of the strip is still inside the
  gate (so the local Fatou estimates apply there);
* `Dstrip_sub_QLeft` is in `Setup.lean`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

/-! ## Membership in the gate -/

/-- **Membership in `Qm ξ α` from real-part conditions.**  If `(z - (ξ - 1/α)).re > 0` and
`z.re + ξ < 0` then `z` is in the gate `Qm ξ α = Qreg (ξ - 1/α) (-ξ)`: the first condition makes
the left cone condition automatic, the second the right one. -/
theorem mem_Qm_of_re {α : ℂ} {ξ : ℝ} {z : ℂ}
    (h1 : 0 < z.re - ξ + (1 / α).re) (h2 : z.re + ξ < 0) : z ∈ Work.Pert.Qm ξ α := by
  have hb1 : (0 : ℝ) < (z - ((ξ : ℂ) - 1 / α)).re := by
    have he : (z - ((ξ : ℂ) - 1 / α)).re = z.re - ξ + (1 / α).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      ring
    rw [he]; exact h1
  have hb2 : (z - (-(ξ : ℂ))).re < 0 := by
    have he : (z - (-(ξ : ℂ))).re = z.re + ξ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
      ring
    rw [he]; exact h2
  rw [Work.Pert.Qm, MandelDim.Qreg]
  constructor
  · intro b hb
    rw [Option.mem_some_iff] at hb
    subst hb
    have := abs_nonneg (z - ((ξ : ℂ) - 1 / α)).im
    linarith
  · intro b hb
    rw [Option.mem_some_iff] at hb
    subst hb
    have := abs_nonneg (z - (-(ξ : ℂ))).im
    linarith

/-- The same, for a ball: if a ball around `z` of radius `ρ` satisfies the two real conditions
uniformly, then it is contained in the gate. -/
theorem ball_sub_Qm {α : ℂ} {ξ ρ : ℝ} {z : ℂ}
    (h1 : (z.re - ρ) - ξ + (1 / α).re > 0) (h2 : z.re + ρ + ξ < 0) :
    Metric.ball z ρ ⊆ Work.Pert.Qm ξ α := by
  intro v hv
  have hv' : ‖v - z‖ < ρ := by
    rw [Metric.mem_ball, dist_eq_norm] at hv
    exact hv
  have h1' : |(v - z).re| ≤ ‖v - z‖ := Complex.abs_re_le_norm _
  have h2' : |(v - z).im| ≤ ‖v - z‖ := Complex.abs_im_le_norm _
  have hvr : |(v - z).re| < ρ := lt_of_le_of_lt h1' hv'
  have hvrl : z.re - ρ < v.re := by
    have h := (abs_lt.mp hvr).1
    have he : (v - z).re = v.re - z.re := Complex.sub_re v z
    rw [he] at h
    linarith
  have hvru : v.re < z.re + ρ := by
    have h := (abs_lt.mp hvr).2
    have he : (v - z).re = v.re - z.re := Complex.sub_re v z
    rw [he] at h
    linarith
  refine mem_Qm_of_re (z := v) ?_ ?_
  · linarith
  · linarith

/-- A ball of radius `M/4` around a point of the deep strip stays in the gate, provided
`Re (1/α)` is large and `M > 4ξ/3`. -/
theorem Dstrip_ball_sub_Qm {M T : ℝ} {α : ℂ} {ξ : ℝ} (hM : 2 ≤ M)
    (hMξ : 3 * M / 4 > ξ) (hα : (5 * M / 4 + 1 + ξ) < (1 / α).re) {u : ℂ}
    (hu : u ∈ Dstrip M T) :
    Metric.ball u (M / 4) ⊆ Work.Pert.Qm ξ α := by
  obtain ⟨h1, h2, -⟩ := hu
  refine ball_sub_Qm (ρ := M / 4) (z := u) ?_ ?_
  · have : (-5 * M / 4 - 1) - ξ + (1 / α).re ≤ (u.re - M / 4) - ξ + (1 / α).re := by linarith
    linarith
  · linarith

/-! ## The anchor region: a fixed compact deep region -/

/-- The anchor region: the closed ball of radius `M/8` around `-M` (all points of the deep strip
with heights `|Im| ≤ M/8` lie in it, and it is a fixed compact subset of the gate). -/
def Danchor (M : ℝ) : Set ℂ := Metric.closedBall (((-M : ℝ)) : ℂ) (M / 4)

theorem Dstrip_sub_Danchor {M T : ℝ} (hM : 8 ≤ M) (hT : T ≤ M / 8) :
    Dstrip M T ⊆ Danchor M := by
  intro u hu
  obtain ⟨h1, h2, h3⟩ := hu
  rw [Danchor, Metric.mem_closedBall, dist_eq_norm]
  have hre : |(u - (((-M : ℝ)) : ℂ)).re| ≤ M / 8 := by
    have he : (u - (((-M : ℝ)) : ℂ)).re = u.re + M := by simp
    rw [he, abs_le]
    constructor <;> linarith
  have him : |(u - (((-M : ℝ)) : ℂ)).im| ≤ M / 8 := by
    have he : (u - (((-M : ℝ)) : ℂ)).im = u.im := by simp
    rw [he]; exact le_trans h3 hT
  calc ‖u - (((-M : ℝ)) : ℂ)‖ ≤ |(u - (((-M : ℝ)) : ℂ)).re| + |(u - (((-M : ℝ)) : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ M / 8 + M / 8 := add_le_add hre him
    _ ≤ M / 4 := by linarith

end

end Work.Pert.Ksub2
