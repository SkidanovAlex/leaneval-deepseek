import Mathlib
import Submission.E2cParam
import Submission.E2cGeom
import Submission.DStar
import Submission.BranchW
import Submission.Rays
import Submission.XTransfer
import Submission.PolyMoment
import Submission.E0Complex
import Submission.HankelDecay
import Submission.PolyaCore
import Submission.Dictionary
import Submission.Conjugates
import Submission.Minpoly
import Submission.GOnCutPlane
import Submission.Gnorm

/-!
# E2c: HedgehogBound + BranchX laurent data ⟹ hankelDet eventually zero

THEOREM (`hankelDet_zero_of_hedgehogBound`): for a NumberField `K` and a
nonzero algebraic integer `α`, if `HedgehogBound (conjugateValues α)` holds
(monic polynomials decaying on a fattening of the hedgehog `star S`,
`S := conjugateValues α` — supplied by E1), then the formal square-root
sequence `a` of `Gpoly (minpoly ℤ α)` (the coefficients of the integer
series from `PowRev.powRev_sqrt_integral`, i.e. the BranchX laurent data)
has Hankel determinants `hankelDet a k = 0` for all large `k`.

WIRING (see Plan.md DESIGN NOTES 63--65): unpack hhb + the BranchX data,
choose the deformation parameters (δ/u/B/A) by `E2cParam`, apply
`DStar.deformation_star` to the circle integral of
`h := g·p_i·p_j·(·)⁻¹`, bound the deformed-contour pieces by
`E2cGeom.fatStar_of_rot_point` / `fatStar_gap_point` (+ `Gnorm` for `|g|`),
identify the moment-matrix entries with the circle integrals
(`PolyMoment.cMomentMatrix_eq_circleIntegral`), and feed
`HankelDecay.hankelDet_eventually_zero_of_moment_bound`.

This module currently contains the elementary bound-helper lemmas
(interval-integral norm bounds); the main theorem is assembled here.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators Interval
open Complex

namespace Submission.E2c

open Submission.PolyaCore
open Submission.DirSet
open Submission.E2cGeom
open Submission.E2bCore

/-- Norm of an `arcInt` is bounded by the sup norm on the parameter
interval: `‖arcInt F u c d‖ ≤ C·|d−c|` when `‖F (u + y·I)‖ ≤ C` for all
`y ∈ Ι c d`. -/
lemma arcInt_norm_le (F : ℂ → ℂ) (u c d C : ℝ) (hC : ∀ y : ℝ, y ∈ Ι c d →
    ‖F (u + y * Complex.I)‖ ≤ C) :
    ‖arcInt F u c d‖ ≤ C * |d - c| := by
  unfold arcInt
  exact intervalIntegral.norm_integral_le_of_norm_le_const hC

/-- Norm of a `radInt` is bounded by the sup norm on the parameter
interval: `‖radInt F a b c‖ ≤ C·|b−a|` when `‖F (t + c·I)‖ ≤ C` for all
`t ∈ Ι a b`. -/
lemma radInt_norm_le (F : ℂ → ℂ) (a b c C : ℝ) (hC : ∀ t : ℝ, t ∈ Ι a b →
    ‖F (t + c * Complex.I)‖ ≤ C) :
    ‖radInt F a b c‖ ≤ C * |b - a| := by
  unfold radInt
  exact intervalIntegral.norm_integral_le_of_norm_le_const hC

/-- `|d − c|` for `d := c + 2·δ` (window width) is `2δ` (given `δ ≥ 0`). -/
lemma abs_sub_of_window {c δ : ℝ} (hδ0 : 0 ≤ δ) :
    |(c + 2 * δ) - c| = 2 * δ := by
  rw [abs_of_nonneg]
  · ring
  · nlinarith

end Submission.E2c

end
