import Mathlib
import Submission.Work.Serre.mvDeltaAuxAssembly
import Submission.Work.Serre.mvDeltaAuxCupNat
import Submission.Work.Serre.MVShift.cupRelChain_homology
import Submission.Work.Serre.MVGlue.mvSetup
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Cohomology.relIncl_relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Mayer–Vietoris `δ`-square for the mixed cup product

This file proves `Work.Serre.cellCupAbs.mvDeltaCupMixedRat`: for an open cover `X = U ∪ V`, a class
`U₀ ∈ H^{n₀}(X,A;ℚ)` and a class `x ∈ H^m(U∩V;ℚ)`, the connecting map `δ` of the rational relative
Mayer–Vietoris sequence is a *derivation* for the mixed cup product:

`(δ_∅ x) ⌣ U₀ = cast (δ_A (x ⌣ U₀|_{U∩V}))`.

This is the statement of `Work.Serre.mvDeltaCupMixedAux` / `Work.Serre.mvDelta_cup_mixed` /
`Work.Serre.MVGlue.mvDeltaCupMixed` (the `(DELTA)` square, the key input of the local-to-global
gluing of the cup map, `Work.Serre.MVGlue.glueCupIso`).

**The proof** is purely assembly, glued from the pieces that are on disk:

* `Work.Serre.deltaSquare` (`mvDeltaAuxAssembly`, proved): the square for a *relative cocycle*
  `t ∈ C^{n₀}(X,A;ℚ)`, whose two hypothesis families are here discharged by the proved
  * four chain-level naturality squares `Work.Serre.mvDeltaAuxCupNat_1..4`, and
  * identification of the homology of the honest cup with the mixed cup product,
    `Work.Serre.MVShift.cupRelChain_homology`;

the passage from a cocycle to an arbitrary class uses `Work.Cohomology.exists_relClassOf`, the
compatibility of the restriction with `relClassOf` (`Work.Serre.restrU_relClassOf`,
`Work.Serre.restrUVU_relClassOf`, `Work.Serre.ovlClass_relClassOf`, all proved) and the identity of
the two spellings of the overlap restriction `Work.Serre.U₀ovl_eq_relCohMap` (proved).  No part of
the comparison `ThetaCmp` is computed anywhere: everything not available by construction is one of
the listed, already-proved lemmas.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.cellCupAbs

noncomputable section

/-- **The rational Mayer–Vietoris connecting map is a derivation for the mixed cup product.**

For an open cover `X = U ∪ V`, a class `U₀ ∈ H^{n₀}(X,A;ℚ)` and a class `x ∈ H^m(U ∩ V;ℚ)`,

`(δ_∅ x) ⌣ U₀ = cast (δ_A (x ⌣ U₀|_{U ∩ V}))`,

where `δ_T = Work.Serre.mvDelta X T U V …` is the connecting map of the pair `(X,T)`. -/
theorem mvDeltaCupMixedRat (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (m : ℕ) (x : Work.Serre.mvCohUV X (∅ : Set X) U V m) :
    (Work.Thom.mixedCupC ℚ A (m + 1) n₀)
        ((Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)).hom
          ((Work.Serre.mvDelta X (∅ : Set X) U V hU hV hcov m).hom x)) U₀
      = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (by omega : (m + n₀) + 1 = (m + 1) + n₀))).hom
          ((Work.Serre.mvDelta X A U V hU hV hcov (m + n₀)).hom
            ((Work.Thom.mixedCupC ℚ (Work.Cohomology.interAU A (U ∩ V)) m n₀)
              ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m).hom x)
              ((Work.Serre.mvRestrUVU X A U V n₀).hom
                ((Work.Serre.mvRestrU X A U n₀).hom U₀)))) := by
  classical
  -- a cocycle representative of `U₀`
  obtain ⟨t, ht, hcls⟩ := Work.Cohomology.exists_relClassOf ℚ X A n₀ U₀
  -- the four chain-level naturality squares and the identification of the homology of the honest cup
  have h1 := Work.Serre.mvDeltaAuxCupNat_1 X A U V n₀ t ht
  have h1V := Work.Serre.mvDeltaAuxCupNat_2 X A U V n₀ t ht
  have h2 := Work.Serre.mvDeltaAuxCupNat_3 X A U V n₀ t ht
  have h2V := Work.Serre.mvDeltaAuxCupNat_4 X A U V n₀ t ht
  have hHomX := Work.Serre.MVShift.cupRelChain_homology X A n₀ t ht
  have hHomUV := Work.Serre.MVShift.cupRelChain_homology (TopCat.of ↥(U ∩ V))
    (Work.Cohomology.interAU A (U ∩ V)) n₀ (Work.Serre.cupTgtUV X A U V n₀ t)
    (Work.Serre.cupTgtUV_cocycle X A U V n₀ t ht)
  -- the `δ`-square for the representative `t`
  have hsq := Work.Serre.deltaSquare X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V hHomX hHomUV m
  -- the overlap restriction of the class, in the two spellings
  have hovl : Work.Cohomology.relClassOf ℚ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V)) (Work.Serre.cupTgtUV X A U V n₀ t)
        (Work.Serre.cupTgtUV_cocycle X A U V n₀ t ht)
      = (Work.Serre.mvRestrUVU X A U V n₀).hom ((Work.Serre.mvRestrU X A U n₀).hom U₀) := by
    rw [← Work.Serre.ovlClass_relClassOf X A U V n₀ t ht, hcls]
  -- evaluate the square at `x` and rewrite the two classes
  have hx := congrArg (fun (f : Work.Serre.mvCohUV X (∅ : Set X) U V m ⟶
      Work.Thom.RelCoh ℚ (m + 1 + n₀) X A) => f.hom x) hsq
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  rw [hcls, hovl] at hx
  exact hx

/-- **The `δ`-square in the spelling of `Work.Serre.mvDeltaCupMixedAux` / `mvDelta_cup_mixed` /
`Work.Serre.MVGlue.mvDeltaCupMixed`** (targets of the three `sorry`-carrying files of the area):
same statement, with the overlap written as the set-builder `{y | (y : X) ∈ A}` and the restricted
class as the direct `relCohMap`.  It is the previous theorem after the two rewrites relating the
spellings (`rfl` for the set, `Work.Serre.U₀ovl_eq_relCohMap` for the class). -/
theorem mvDeltaCupMixedAuxForm (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
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
  have hsp : Work.Serre.mvRestrU X A U n₀ ≫ Work.Serre.mvRestrUVU X A U V n₀
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
        ({y : ↥(U ∩ V) | (y : X) ∈ A}) A (fun _ hy => hy) ℚ n₀ := by
    rw [show Work.Serre.mvRestrUVU X A U V n₀ = Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          (Work.Cohomology.interAU A (U ∩ V)) (Work.Cohomology.interAU A U)
          (fun _ hx => hx) ℚ n₀ from rfl,
      show Work.Serre.mvRestrU X A U n₀ = Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          (Work.Cohomology.interAU A U) A (fun _ hy => hy) ℚ n₀ from rfl,
      Work.Thom.relCohMap_compA (Work.Cohomology.interAU A (U ∩ V))
          (Work.Cohomology.interAU A U) A
          (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ n₀]
    exact (Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) (fun x hx => hx) (fun x hx => hx)
        ℚ n₀).trans
      (Work.Thom.relCohMap_hcongrA _ _ _ (fun x hx => hx) (fun x hx => hx) ℚ n₀)
  rw [← hsp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact mvDeltaCupMixedRat X A U V hU hV hcov n₀ U₀ m x

end

end Work.Serre.cellCupAbs
