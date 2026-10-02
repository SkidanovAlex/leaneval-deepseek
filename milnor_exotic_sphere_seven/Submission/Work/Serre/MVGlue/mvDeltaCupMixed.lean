import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Serre.cellCupAbs.mvDeltaCupMixedRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Mayer--Vietoris `δ`-square for the mixed cup product (legacy spelling)

`Work.Serre.MVGlue.mvDeltaCupMixed` is the *legacy* spelling of the `(DELTA)` square — the same
statement as `Work.Serre.cellCupAbs.mvDeltaCupMixedRat`
(`Submission/Work/Serre/cellCupAbs/mvDeltaCupMixedRat.lean`, PROVED from the chain-level naturality
squares `Work.Serre.mvDeltaAuxCupNat_1..4` and `Work.Serre.MVShift.cupRelChain_homology`) and as the
ladder form `Work.Serre.mvDeltaCupMixed` (`Submission/Work/Serre/mvDeltaCupMixed.lean`, PROVED).

The only difference is the spelling of the restriction of `U₀` to the overlap: here it is written as
the single `relCohMap` along `U ∩ V ↪ X`, in the other files as the composite
`Work.Serre.mvRestrUVU ≫ Work.Serre.mvRestrU`.  The two agree by the proved
`Work.Serre.U₀ovl_eq_relCohMap`.

This file used to contain a `sorry`; it is now a one-line consequence of the proved spelling, so the
whole `Work.Serre.MVGlue` cluster is axiom-clean.
-/

namespace Work.Serre.MVGlue

theorem mvDeltaCupMixed
    (X : TopCat) (A : Set X) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (m : ℕ) (x : Work.Serre.mvCohUV X (∅ : Set X) U V m) :
    (Work.Thom.mixedCupC ℚ A (m + 1) n₀)
        ((Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)).hom
          ((Work.Serre.mvDelta X (∅ : Set X) U V hU hV hcov m).hom x)) U₀
      = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (by omega : (m + n₀) + 1 = (m + 1) + n₀))).hom
          ((Work.Serre.mvDelta X A U V hU hV hcov (m + n₀)).hom
            ((Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀)
              ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m).hom x)
              ((Work.Thom.relCohMap
                (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
                {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) := by
  have h := Work.Serre.cellCupAbs.mvDeltaCupMixedRat X A U V hU hV hcov n₀ U₀ m x
  rw [show (Work.Serre.mvRestrUVU X A U V n₀).hom
        ((Work.Serre.mvRestrU X A U n₀).hom U₀)
      = (Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀
      from Work.Serre.U₀ovl_eq_relCohMap X A U V n₀ U₀] at h
  exact h

end Work.Serre.MVGlue
