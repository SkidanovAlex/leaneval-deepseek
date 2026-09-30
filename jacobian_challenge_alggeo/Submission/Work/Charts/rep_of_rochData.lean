/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The surjectivity `Sym^g C → Pic⁰` (the `rep` input of `Charts_of_sym_cover`)

For a base divisor `P₀` of degree one, the map `D ↦ [divOf D] - g · [P₀]` from the `F`-points of
`Sym^g C` onto the degree-zero classes is *surjective*: given a class `c = [A]` with `deg A = 0`,
the divisor `A + g · P₀` has degree `g`, so by RR7 (`RochData_exists_effective_deg`) it has an
effective representative `E` of degree `g`, which is `divOf D` for a *unique* point `D` of
`Sym^g C` (`SymGeom.divOf_complete`).

This discharges the hypothesis `rep` of `Work.Charts.Charts_of_sym_cover` from
`Work.Charts.RochData`, so that COV follows from the *geometric* covering of `Sym^g` alone.
-/
import Submission.Work.Charts.Core
import Submission.Work.Charts.RochData_exists_effective_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped Classical MonoidalCategory

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- **The `rep` hypothesis of `Charts_of_sym_cover`, from Riemann–Roch.**  Every degree-zero
class is `[divOf D] - g · [P₀]` for some point `D` of `Sym^g C`. -/
theorem rep_of_rochData {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0Div : Dv C K) (hP0deg : Ddeg C K P0Div = 1) :
    ∀ {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F),
      ∃ (D : FPt (Sym C R.g) F) (hD : Ddeg C F (divOf D - (R.g : ℤ) • pullK C P0Div) = 0),
        Pic0.mk (divOf D - (R.g : ℤ) • pullK C P0Div) hD = c := by
  intro F _ _ c
  have hdegP : Ddeg C F (pullK C P0Div) = 1 := by
    have h := Work.SpecLin.DivBase.deg_bc (C := C) (e := IsScalarTower.toAlgHom K K F) P0Div
    show Ddeg C F (Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) P0Div) = 1
    rw [← hP0deg]
    exact h
  revert c
  refine Quotient.ind (fun x => ?_)
  obtain ⟨A, hA⟩ := x
  set B : Dv C F := A + (R.g : ℤ) • pullK C P0Div with hB
  have hz : Ddeg C F ((R.g : ℤ) • pullK C P0Div) = (R.g : ℤ) := by
    rw [Ddeg_smul, hdegP, mul_one]
  have hdegB : (R.g : ℤ) ≤ Ddeg C F B := by
    rw [hB, Ddeg_add, hz, hA, zero_add]
  obtain ⟨E, hEeff, hEdeg, hElin⟩ := RochData_exists_effective_deg R B hdegB
  have hEdeg' : Ddeg C F E = (R.g : ℤ) := by
    rw [hEdeg, hB, Ddeg_add, hz, hA, zero_add]
  obtain ⟨D, hD⟩ := Work.SpecLin.SymGeom.divOf_complete (C := C) (n := R.g) E hEeff hEdeg'
  subst hD
  refine ⟨D, ?_, ?_⟩
  · change Ddeg C F (Work.SpecLin.SymGeom.divOf D - (R.g : ℤ) • pullK C P0Div) = 0
    rw [Ddeg_sub, hEdeg', hz, sub_self]
  · change Pic0.mk (Work.SpecLin.SymGeom.divOf D - (R.g : ℤ) • pullK C P0Div) _ =
      Pic0.mk A hA
    refine (Pic0.mk_eq_iff _ _).mpr ?_
    have h1 : LinEquiv C (Work.SpecLin.SymGeom.divOf D) B := hElin.symm
    have h3 := (LinEquiv.sub_iff (Work.SpecLin.SymGeom.divOf D) B
      ((R.g : ℤ) • pullK C P0Div)).mpr h1
    have h4 : B - ((R.g : ℤ) • pullK C P0Div) = A := by rw [hB]; abel
    rwa [h4] at h3

end

end Work.Charts
