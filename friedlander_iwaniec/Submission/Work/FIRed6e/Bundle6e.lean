/-
# `Submission.Work.FIRed6e.Bundle6e` — the budget bundle and the τ-removal brick of the amended
composition

The amended composition (`prop41_of_areas6e`) consumes, per far piece and per class mod `8`,

* the *clean* area 6 `Work.FITop4.Area6_6e`, whose `U`-estimate is
  `‖Ucut‖ ≤ cν((Pz)⁻¹+X⁻¹)N²log N`, and
* the τ-removal `Work.FITop4.TauRemoval6` (FI (10.4)), which pays the (5.9) truncation at
  polylogarithmic quality `N²(log N)^{-19·10^8}`.

Because the piece coefficient supplied by the reduction still carries the (5.9) condition
(`IsBetaCoeff6`), the two estimates must be added *before* the per-piece budget is applied: the
per-piece bundle therefore gains one constant `cE` and one summand `cE·N²(log N)^{-σ}` in its
`U`-conjunct.  This file defines that bundle (`AreaBounds6e`), the U-cut as an explicit cut
function, and the single real-analytic step (`Ucut_tauCut_le`) that turns the two estimates on
`βc` and on `tauCut Pa βc` into the `U`-conjunct of the bundle.

Everything here is bookkeeping: no arithmetic.
-/
import Mathlib
import Submission.Work.FITop4.Areas6e
import Submission.Work.FITop4.Areas6c
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Areas6

set_option autoImplicit false

namespace Work.FIRed6e

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The U-cut as an explicit cut function -/

/-- The cut of (10.15) — `d ≤ X` — extracted from `Work.FITop4.Ucut`, so that the τ-removal
`Work.FITop4.TauRemoval6` (which quantifies over every cut bounded by `1`) can be applied to it. -/
def cutU (X : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ := fun _ _ d => if d ≤ X then 1 else 0

/-- `Ucut` is `Tcut` at the cut `cutU`.  Definitional, recorded so that callers can rewrite in
either direction. -/
lemma Ucut_eq_Tcut_cutU (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop4.Ucut Rz X β = Work.FITop4.Tcut Rz (cutU X) β := rfl

/-- The cut `cutU X` is bounded by `1`, the hypothesis under which `TauRemoval6` applies. -/
lemma cutU_abs_le (X : ℕ) (z1 z2 : GaussianInt) (d : ℕ) : |cutU X z1 z2 d| ≤ 1 := by
  unfold cutU
  split <;> norm_num

/-! ## 2. The per-piece bundle with the τ-error slot -/

/-- **The per-piece bundle of the amended composition.**

`Work.FIRed6Axis.AreaBounds6b` with one more constant `cE`: the `U`-conjunct becomes

  `‖Ucut (radN Pa) X β‖ ≤ cU((Pz)⁻¹+X⁻¹)N²log N + cE·N²(log N)^{-σ}`.

The extra summand is the (5.9) τ-removal cost, paid inside the `N²(log N)^{-σ}` (5.25) budget of
the composition (FI (10.4)); see `Submission/Work/FIArea6/AREA6_CONTRACT_LEAD.md` §4.  All other
six conjuncts are those of `AreaBounds6b` verbatim. -/
def AreaBounds6e (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (X : ℕ) (σ : ℝ) (c1 Cb C3b C3 cU cV cW cE : ℝ) : Prop :=
  (∀ f' φ' z0' β', Work.FITop4.IsMajorant6 Pa f' → Work.FITop4.IsBetaCoeff6 Pa φ' z0' β' →
      (‖Work.FITop4.Bstar Pa β' - Work.FITop4.Bfree Pa β'‖
          ≤ c1 * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
              + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
            * (Real.log Pa.N) ^ (3 : ℕ)) ∧
      (Work.FITop4.Dform Pa f' β'
          ≤ Work.FITop4.Dstar Pa f' β'
            + c1 * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
              * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ))) ∧
  (∀ f' φ' z0' β', Work.FITop4.IsMajorant6 Pa f' → Work.FITop4.IsBetaCoeff6 Pa φ' z0' β' →
      ‖Work.FITop4.Dstar Pa f' β' - Work.FITop4.D0 (Work.FITop.radN Pa)
          (Work.FITop3.Fhat Pa f') β'‖
        ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
        + C3b * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
            * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) ∧
  (∀ f' φ' z0' β', Work.FITop4.IsMajorant6 Pa f' → Work.FITop4.IsBetaCoeff6 Pa φ' z0' β' →
      ‖Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f') β'
          - Work.FITop4.cMain6 (Work.FITop3.Fhat Pa f') Pa.N
              * Work.FITop4.Tbeta (Work.FITop.radN Pa) β'‖
        ≤ C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) ∧
  (‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
      ≤ cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2) ∧
  (‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖
      ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        + cE * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ)) ∧
  (‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      ≤ cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)

/-! ## 3. The τ-removal brick -/

/-- `sigmaChoice Asave = 1004194313 ≤ 19·10^8`.  The exponent of the τ-removal error
`Work.FITop4.TauRemoval6` is `19·10^8`, comfortably above the (5.25) exponent `σ = sigmaChoice
Asave` under which the composition consumes it. -/
theorem sigmaChoice_Asave_le : Work.FITop4.sigmaChoice Work.FITop4.Asave ≤ 19 * 10 ^ 8 := by
  unfold Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- For `L ≥ 1`, the τ-removal exponent `-19·10^8` is *below* (i.e. the power is *above*)
`-sigmaChoice Asave`: `L^{-19·10^8} ≤ L^{-σ}`. -/
theorem rpow_neg_19e8_le_sigma {L : ℝ} (hL : 1 ≤ L) :
    L ^ (-(19 * 10 ^ 8 : ℝ)) ≤ L ^ (-(Work.FITop4.sigmaChoice Work.FITop4.Asave)) := by
  apply Real.rpow_le_rpow_of_exponent_le hL
  have h := sigmaChoice_Asave_le
  linarith

/-- **The `U`-slot of `AreaBounds6e`.**  If the clean coefficient `βc` satisfies the area-6
estimate and the τ-removal applies to `tauCut Pa βc − βc`, then `tauCut Pa βc` — which is the
coefficient the reduction hands over — satisfies the area-6 estimate with the τ-error
`cE·N²(log N)^{-σ}` added, at `cE := Cτ` and `σ := sigmaChoice Asave`. -/
theorem Ucut_tauCut_le (Pa : Work.FITop.Params) (X : ℕ) (βc : GaussianInt → ℂ) (cU Cτ : ℝ)
    (hcU : 0 ≤ cU) (hCτ : 0 ≤ Cτ) (hL : 1 ≤ Real.log Pa.N)
    (hU : ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X βc‖
      ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)
    (hτ : ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X (Work.FITop4.tauCut Pa βc)
        - Work.FITop4.Ucut (Work.FITop.radN Pa) X βc‖
      ≤ Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(19 * 10 ^ 8 : ℝ))) :
    ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X (Work.FITop4.tauCut Pa βc)‖
      ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        + Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(Work.FITop4.sigmaChoice Work.FITop4.Asave)) := by
  have hN2 : (0 : ℝ) ≤ Pa.N ^ 2 := sq_nonneg Pa.N
  have hlt := rpow_neg_19e8_le_sigma hL
  have hmono : Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(19 * 10 ^ 8 : ℝ))
      ≤ Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(Work.FITop4.sigmaChoice Work.FITop4.Asave)) :=
    mul_le_mul_of_nonneg_left hlt (mul_nonneg hCτ hN2)
  -- abbreviate the two exact values, so that no rewriting has to reach inside a sum
  set A : ℂ := Work.FITop4.Ucut (Work.FITop.radN Pa) X (Work.FITop4.tauCut Pa βc) with hA
  set B : ℂ := Work.FITop4.Ucut (Work.FITop.radN Pa) X βc with hB
  have htri : ‖A‖ ≤ ‖A - B‖ + ‖B‖ := by
    have h1 : A = (A - B) + B := by ring
    calc ‖A‖ = ‖(A - B) + B‖ := congrArg Norm.norm h1
      _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
  calc ‖A‖ ≤ ‖A - B‖ + ‖B‖ := htri
    _ ≤ Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(19 * 10 ^ 8 : ℝ))
        + cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := add_le_add hτ hU
    _ ≤ Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(Work.FITop4.sigmaChoice Work.FITop4.Asave))
        + cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
        add_le_add hmono (le_refl _)
    _ = cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        + Cτ * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(Work.FITop4.sigmaChoice Work.FITop4.Asave)) := by
        ring

end

end Work.FIRed6e
