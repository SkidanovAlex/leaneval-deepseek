/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Submission.Work.FatouCoord.Basic

/-!
# Quantitative set-up for a parabolic germ

A holomorphic germ `f z = z + z ^ 2 * h z` with `h 0 = 1` is collected in the structure
`ParabolicBounds`, which records the quantitative information the Fatou–Leau construction
uses: an expansion of `h` to second order, boundedness of `h` and of `h'` on a disc.

We also introduce the chart-conjugate dynamics `wMap f w = -1 / f (-1 / w)`, the *approximate*
Abel coordinate `approxCoord c w = w - c * log w`, its defect `coordError`, and the Fatou
coordinate `fatouCoordW` in the `w`-chart (a limit `w - c log w + ∑ coordError (wMap^k w)`)
together with its dynamical-plane version `fatouCoord f c z = fatouCoordW f c (-1/z)`.

Estimates for `wMap`, `coordError` and for `fatouCoordW` are proved in the companion files
`FatouCoord/Estimate/*` and `FatouCoord/Exist/*`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' N C B : ℝ} {z w : ℂ} {c : ℂ}

/-! ## The quantitative hypotheses -/

/-- Quantitative hypotheses for a holomorphic germ with a parabolic fixed point of
multiplicity one at `0`: on the disc of radius `r` the map has the form
`f z = z + z ^ 2 * h z`, `h 0 = 1`, and `h` is close to `1` to second order, bounded, and has
bounded derivative.  In this setting the pull-back `w ↦ -1/f(-1/w)` is a translation by `1` up
to `O(1/w ^ 2)` errors, which is exactly what the Fatou coordinate construction needs. -/
structure ParabolicBounds (f h : ℂ → ℂ) (a : ℂ) (r A A' : ℝ) : Prop where
  hr : 0 < r
  hA : 0 ≤ A
  hA' : 0 ≤ A'
  f_eq : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z
  h_diff : DifferentiableOn ℂ h (ball 0 r)
  h_close : ∀ z ∈ ball 0 r, ‖h z - 1 - a * z‖ ≤ A * ‖z‖ ^ 2
  h_bound : ∀ z ∈ ball 0 r, ‖h z‖ ≤ 2
  h_deriv_bound : ∀ z ∈ ball 0 r, ‖deriv h z‖ ≤ A'

/-! ## Elementary consequences -/

theorem norm_neg_one_div_lt {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (hN : 1 / r < ‖w‖) :
    ‖-1 / w‖ < r := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [norm_div, norm_neg, norm_one, div_lt_iff₀ hn]
  rw [div_lt_iff₀ hr] at hN
  linarith [mul_comm r ‖w‖]

/-- The chart-conjugate dynamics written in terms of the germ: if `f z = z + z ^ 2 * h z`
then `wMap f w = w / (1 + (-1/w) * h (-1/w))`. -/
theorem wMap_eq {r : ℝ} (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hw : 0 < w.re) (hN : 1 / r < ‖w‖) : wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
  have hw0 : w ≠ 0 := by intro hw0; rw [hw0] at hw; simp at hw
  have hz : -1 / w ∈ ball 0 r := by
    simpa [mem_ball_zero_iff] using norm_neg_one_div_lt hr hw0 hN
  have hzw : -1 / (-1 / w) = w := by field_simp
  have h1 : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
    rw [hf (-1 / w) hz]; ring
  simp only [wMap, chart]
  rw [h1, div_mul_eq_div_div, hzw]

/-- The "defect" `wMap f w - w` of the pull-back from being a translation. -/
theorem wMap_sub_eq {r : ℝ} (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hw : 0 < w.re) (hN : 1 / r < ‖w‖) (hne : 1 + (-1 / w) * h (-1 / w) ≠ 0) :
    wMap f w - w = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by
  have hw0 : w ≠ 0 := by intro hw0; rw [hw0] at hw; simp at hw
  have key : w * ((-1 / w) * h (-1 / w)) = -h (-1 / w) := by field_simp
  have hsub : (wMap f w - w) * (1 + (-1 / w) * h (-1 / w)) = h (-1 / w) := by
    rw [wMap_eq hr hf hw hN, sub_mul, div_mul_cancel₀ _ hne]
    rw [show w - w * (1 + (-1 / w) * h (-1 / w))
        = -(w * ((-1 / w) * h (-1 / w))) by ring, key, neg_neg]
  calc wMap f w - w
      = ((wMap f w - w) * (1 + (-1 / w) * h (-1 / w))) / (1 + (-1 / w) * h (-1 / w)) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by rw [hsub]

/-! ## The approximate coordinate and its defect -/

/-- The approximate Abel coordinate in the `w`-chart: `w - c * log w`.  The classical
asymptotic is `ψ(w) = w - c log w + O(1/w)` with `c = 1 - a` (where `a = h'(0)`). -/
def approxCoord (c : ℂ) (w : ℂ) : ℂ := w - c * Complex.log w

/-- The defect of `approxCoord` with respect to the Abel equation in the chart. -/
def coordError (f : ℂ → ℂ) (c : ℂ) (w : ℂ) : ℂ :=
  approxCoord c (wMap f w) - approxCoord c w - 1

theorem approxCoord_apply (w : ℂ) : approxCoord c w = w - c * Complex.log w := rfl

theorem coordError_apply (w : ℂ) :
    coordError f c w = approxCoord c (wMap f w) - approxCoord c w - 1 := rfl

/-- The defect is the sum of the translation error of `wMap` and the logarithm defect. -/
theorem coordError_eq (w : ℂ) :
    coordError f c w = (wMap f w - w - 1) - c * (Complex.log (wMap f w) - Complex.log w) := by
  simp only [coordError, approxCoord]
  ring

theorem deriv_approxCoord {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    deriv (approxCoord c) w = 1 - c / w := by
  have h1 : HasDerivAt (approxCoord c) (1 - c / w) w := by
    have hlog : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hw
    have h3 : HasDerivAt (fun w : ℂ => w - c * Complex.log w) (1 - c * w⁻¹) w :=
      (hasDerivAt_id w).sub (hlog.const_mul c)
    convert h3 using 2
    · simp [approxCoord]
    · rw [div_eq_mul_inv]
  exact h1.deriv

/-! ## The Fatou coordinate in the `w`-chart and in the dynamical plane -/

/-- The Fatou coordinate in the chart `w = -1/z`, obtained from the approximate coordinate by
adding the sum of the defects along the orbit.  On the domain where the defects are `O(1/w^2)`
this converges absolutely and defines a holomorphic function satisfying
`ψ (wMap f w) = ψ w + 1`; see `FatouCoord/Exist/fatouCoordW_abel`. -/
def fatouCoordW (f : ℂ → ℂ) (c : ℂ) (w : ℂ) : ℂ :=
  approxCoord c w + ∑' k : ℕ, coordError f c ((wMap f)^[k] w)

/-- The Fatou coordinate in the dynamical plane: `φ z = ψ (-1/z)`. -/
def fatouCoord (f : ℂ → ℂ) (c : ℂ) (z : ℂ) : ℂ := fatouCoordW f c (chart z)

theorem fatouCoord_eq (z : ℂ) : fatouCoord f c z = fatouCoordW f c (chart z) := rfl

theorem fatouCoordW_eq (w : ℂ) :
    fatouCoordW f c w = approxCoord c w + ∑' k : ℕ, coordError f c ((wMap f)^[k] w) := rfl

end

end Work.FatouCoord
