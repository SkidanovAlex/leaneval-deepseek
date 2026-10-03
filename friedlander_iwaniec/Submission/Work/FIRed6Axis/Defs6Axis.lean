/-
# `Submission.Work.FIRed6Axis.Defs6Axis` — the near/far angular vocabulary of the axis repair

*FI* p. 970, immediately after (5.16):

> We can assume that `|φ mod π/2| > πϑ` because the other sectors, altogether of angle `≤ 2πϑ`,
> contribute no more than the bound (4.23) by the estimate (5.16).

The round-6 area contract (`FITop4.Defs6`) puts the *sector-scale* axis condition
`IsAxisFree Pa z := Pa.ϑ√(Pa.N) < |Re z| ∧ Pa.ϑ√(Pa.N) < |Im z|` into the support of the coefficient
`IsBetaCoeff6`, hence into the hypothesis of every area.  The §§4–5.2 reduction produces cell
coefficients that satisfy only the round-4 `IsBetaCoeff`; the two are bridged by

* **removing the near-axis cells of the angular partition *before* the Cauchy–Schwarz step**, where
  they are bounded by the trivial box bound (5.16) (`NearAxisBound` in `Statement.lean`), and
* **class-splitting the far cells**, each of whose support is axis-free by construction
  (`FarPiece_isAxisFree` below).

This file holds the vocabulary: the far-sector condition on the boundary `φ` of a cell, the
far-support condition on a whole cell (`FarPiece`), the near-zone predicate `nearArg` and the cell
region `InSector`, together with the elementary transfers that the reduction and the class split
consume.

Conventions: a *cell* (polar box of (5.14)) is `{N < |z|² ≤ (1+θ)N, φ < arg z ≤ φ + 2πθ}` and the
angular distance to the axes is measured to `(π/2)ℤ` (`ℝ` arguments, `arg : ℂ → (-π,π]`).
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop6.Sector.arg_dist_implies_axisFree

set_option autoImplicit false

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The vocabulary -/

/-- **The far-sector condition on the boundary `φ` of an angular cell.**  The cell
`(φ, φ + 2πθ]` is at angular distance `≥ 2ϑ + 2πθ` from every multiple of `π/2`, so that *every*
point of the cell is at distance `≥ 2ϑ` from the axes. -/
def farAngle (ϑ θ φ : ℝ) : Prop :=
  ∀ m : ℤ, 2 * ϑ + 2 * Real.pi * θ ≤ |φ - (m : ℝ) * (Real.pi / 2)|

/-- **The far-support condition on a cell** `(Pa, φ)`: every point of the polar box (5.14) is at
angular distance `≥ 2·Pa.ϑ` from every multiple of `π/2`.  This is the clause carried by every
piece of `reduction_save6_axis`. -/
def FarPiece (Pa : Work.FITop.Params) (φ : ℝ) : Prop :=
  ∀ z : GaussianInt, Work.FITop4.InPolarBox Pa φ z →
    ∀ m : ℤ, 2 * Pa.ϑ ≤ |Complex.arg z.toComplex - (m : ℝ) * (Real.pi / 2)|

/-- **The near-axis zone of angular width `2c`** around the four axes: `arg z` is within `c` of a
multiple of `π/2`. -/
def nearArg (c : ℝ) (z : GaussianInt) : Prop :=
  ∃ m : ℤ, |Complex.arg z.toComplex - (m : ℝ) * (Real.pi / 2)| ≤ c

/-- **The restriction of a coefficient to the class of `z₀` modulo eight** (5.7): the coefficient
`z ↦ (if z ≡ z₀ (mod 8) then β z else 0)`.  (Defining it here keeps the `Decidable` instance for
`SameClass8` out of the callers' statements.) -/
def clsRestrict (z0 : GaussianInt) (β : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z => if Work.FITop4.SameClass8 z z0 then β z else 0

/-- The bare cell region `{N < |z|² ≤ (1+θ)N, φ < arg z ≤ φ + 2πθ}` (the polar box of (5.14) without
the primitivity condition of (5.3)); used by the counting lemmas. -/
def InSector (N θ : ℝ) (φ : ℝ) (z : GaussianInt) : Prop :=
  N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (1 + θ) * N ∧
    φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ

/-! ## 2. Elementary API -/

/-- `π / 2 < 2`. -/
lemma half_pi_lt_two : Real.pi / 2 < 2 := by
  have := Real.pi_lt_four
  linarith

/-- `log 3 > 1`. -/
lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  rwa [Real.log_exp] at h

/-- The saving factor of (4.16) is at most one. -/
lemma vartheta_le_one (Pa : Work.FITop.Params) : Pa.ϑ ≤ 1 := by
  rw [Pa.hϑ]
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : 1 ≤ Real.log (Pa.x : ℝ) :=
    le_of_lt (lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hx3))
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (neg_nonpos.mpr Pa.hA.le)

/-- **A far sector is a far cell.**  The cell boundary `φ` being at distance `≥ 2ϑ + 2πθ` from the
axes forces every point of the cell to be at distance `≥ 2ϑ` from the axes (reverse triangle
inequality on the angular coordinate). -/
lemma farAngle_farPiece {Pa : Work.FITop.Params} {φ : ℝ}
    (h : farAngle Pa.ϑ Pa.θ φ) : FarPiece Pa φ := by
  intro z hz m
  have harglo : φ < Complex.arg z.toComplex := hz.2.2.2.1
  have hargle : Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ := hz.2.2.2.2
  have h3 : |Complex.arg z.toComplex - φ| ≤ 2 * Real.pi * Pa.θ := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htri := abs_sub_abs_le_abs_sub (φ - (m : ℝ) * (Real.pi / 2))
    (Complex.arg z.toComplex - (m : ℝ) * (Real.pi / 2))
  have heq : (φ - (m : ℝ) * (Real.pi / 2)) - (Complex.arg z.toComplex - (m : ℝ) * (Real.pi / 2))
      = φ - Complex.arg z.toComplex := by ring
  rw [heq, abs_sub_comm φ (Complex.arg z.toComplex)] at htri
  have h4 := h m
  linarith

/-- **A far cell is axis-free**: every point of the polar box of a far piece satisfies the round-6
`IsAxisFree` (`ϑ√N < |Re z|, |Im z|`).  This is the transfer that lets the class-split of a far
piece produce `IsBetaCoeff6` coefficients.

The angular input is `Work.FITop6.Sector.arg_dist_implies_axisFree` (FITop6), applied after
upgrading the distance `≥ 2ϑ` to the strict distance `> πϑ/2` used there (`π/2 < 2`). -/
lemma FarPiece_isAxisFree {Pa : Work.FITop.Params} {φ : ℝ} (h : FarPiece Pa φ)
    {z : GaussianInt} (hz : Work.FITop4.InPolarBox Pa φ z) : Work.FITop4.IsAxisFree Pa z := by
  refine Work.FITop6.Sector.arg_dist_implies_axisFree hz.2.1 ?_ (vartheta_le_one Pa)
  intro m
  have h2 := h z hz m
  have hp : Real.pi * Pa.ϑ / 2 < 2 * Pa.ϑ := by
    nlinarith [Pa.hϑ0, half_pi_lt_two]
  linarith

end

end Work.FIRed6Axis
