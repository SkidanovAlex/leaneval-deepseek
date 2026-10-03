/-
# `Submission.Work.FIRed6Axis.prop41of.Bundle` — the local per-piece bundle of the axis repair
composition

The composition `Work.FIRed6Axis.prop41_of_areas6_of` cannot consume the frozen per-piece bundle
`Work.FITop4.AreaBounds6`: its second conjunct is the round-6 `Area2_6` (9.10), which is *strictly
stronger* than the repaired `Area2_6b` that the round-6 contract actually supplies (the lead's
2026-09-27 change): `Area2_6b` bounds `‖D* − D₀‖` by `Area2_6`'s right-hand side **plus** the
(7.10)/(10.4) replacement error `C3'·(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`, which has exactly the
shape of `Area3_6`'s error.

This file therefore defines the local (non-frozen) copy of the bundle, with the second conjunct
taken from `Area2_6b` and the extra constant `C3b` sitting next to `Area3_6`'s `C3`; the two are
absorbed together by the `NumHyp` side conditions of `Work.FITop4.Red5.numHyp_proof_save`
(see `Work.FIRed6Axis.Dform_le_budget6b`).

Also here: the pointwise identification of `clsRestrict (rep8 c) β` with the `cls8`-cut of `β`,
which is the form in which `Work.FITop4.Dform_classSplit` splits `Dform`.
-/
import Mathlib
import Submission.Work.FIRed6Axis.Statement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The per-piece bundle of the composition, with `Area2_6b` in place of `Area2_6`.**

Exactly `Work.FITop4.AreaBounds6` with its second conjunct replaced by the conclusion of
`Work.FITop4.Area2_6b`: it bounds `‖D* − D₀‖` by `Cb·ϑ⁻¹τ²N²(log N)^{b(η)}` **plus**
`C3b·(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`, the extra (7.10)/(10.4) replacement error.  The
first, third, fourth, fifth and sixth conjuncts are verbatim those of `AreaBounds6`. -/
def AreaBounds6b (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (X : ℕ) (σ : ℝ) (c1 Cb C3b C3 cU cV cW : ℝ) : Prop :=
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
      ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) ∧
  (‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      ≤ cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)

/-- **`clsRestrict (rep8 c)` is the `cls8`-cut of `β`**: the form in which
`Work.FITop4.Dform_classSplit` splits `Dform` (`if cls8 z = c then β z else 0`). -/
lemma clsRestrict_rep8_eq (c : ZMod 8 × ZMod 8) (β : GaussianInt → ℂ) :
    clsRestrict (Work.FITop4.rep8 c) β
      = fun z => if Work.FITop4.cls8 z = c then β z else 0 := by
  funext z
  simp only [clsRestrict, Work.FITop4.sameClass8_rep8_iff]

end

end Work.FIRed6Axis
