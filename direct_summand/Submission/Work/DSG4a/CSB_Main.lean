import Mathlib
import Submission.Work.DSG4a.CSB_Defs
import Submission.Work.DSG4a.cechZ_baseChange
import Submission.Work.DSG4a.quasiIso_baseChangeComplexFunctor
import Submission.Work.DSG4a.isKProjective_baseChangeComplexFunctor
import Submission.Work.DSEQ0.singleZ_isKProjective
import Submission.Work.DSG4a.chainSplitBC.quotient_map_eq_of_Q_map_eq_comp
import Submission.Work.DSG4a.chainSplitBC.cechZ_baseChange_coaug_eq

/-!
# `chainSplit_baseChange_iff` — the derived comparison

This file contains the derived-category part of the proof of
`Work.DSG4a.chainSplit_baseChange_iff`: the coaugmentation `cc' : A'[0] ⟶ P ⊗[A] A'` of the
base-changed model, which is a lift of the Čech coaugmentation of `X_{A'}` along
`q_b = (baseChangeComplexFunctor).map q ≫ Φ`, represents in the derived category the same
morphism as the base change `ccBase P cc` of the coaugmentation `cc` of `P`.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.DSG4a

universe u

/-- **Equal images in the homotopy category give equal images in the derived category.** -/
theorem Q_map_eq_of_quotient_map_eq {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    {f g : K ⟶ L}
    (h : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map f =
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g := by
  refine (cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app K)).mp ?_
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality f,
    ← DerivedCategory.quotientCompQhIso_hom_naturality g, h]

/-- **The coaugmentation lifted along the base-changed quasi-isomorphism is the base change of
the canonical coaugmentation**, at the level of the derived category.

The proof is the one recorded in the recipe of `chainSplit_baseChange_iff`: the chain-level
coherence `ccAn' = eS ≫ (baseChangeComplexFunctor).map ccAn ≫ Φ`
(`Work.DSG4a.chainSplitBC.cechZ_baseChange_coaug_eq`), the fact that `cc ≫ q` is homotopic to
`ccAn` (from `hlift`, using K-projectivity of the source `A[0]`), and the fact that
`(baseChangeComplexFunctor).map q ≫ Φ` becomes an isomorphism in the derived category
(flatness and the quasi-isomorphisms `q`, `Φ`). -/
theorem Q_map_ccBase {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} A')]
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    {ι : Type u} [Finite ι] [Nonempty ι]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hflat : Module.Flat A A')
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective]
    (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (cc : Work.DSG4a.singleZ A ⟶ P) (ccAn : Work.DSG4a.singleZ A ⟶ DSMap.cechZ A X f U)
    (hccAn : Work.DSG4a.coaugClause X f U ccAn)
    (hlift : DerivedCategory.Q.map ccAn = DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map q)
    (ccAn' : Work.DSG4a.singleZ A' ⟶ DSMap.cechZ A' (Work.DSG4a.baseChangeScheme X f)
      (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (hccAn' : Work.DSG4a.coaugClause (Work.DSG4a.baseChangeScheme X f)
      (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)) ccAn')
    (Φ : Work.DSG4a.baseChangeComplex (A := A) (A' := A') (DSMap.cechZ A X f U) ⟶
      DSMap.cechZ A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
        (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (hΦq : QuasiIso Φ)
    (hΦ : ∀ a' : A', (Φ.f 0) (a' ⊗ₜ[A, algebraMap A A'] Work.DSG4a.coaugZElem A X f U) =
      a' • Work.DSG4a.coaugZElem A' (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (cc' : Work.DSG4a.singleZ A' ⟶ Work.DSG4a.baseChangeComplex (A := A) (A' := A') P)
    (hlift' : DerivedCategory.Q.map ccAn' = DerivedCategory.Q.map cc' ≫
      DerivedCategory.Q.map ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫
        Φ)) :
    DerivedCategory.Q.map cc' = DerivedCategory.Q.map (Work.DSG4a.ccBase P cc) := by
  haveI hIso1 : IsIso (DerivedCategory.Q.map
      ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A') _).mpr
      (Work.DSG4a.quasiIso_baseChangeComplexFunctor hflat q hq)
  haveI hIso2 : IsIso (DerivedCategory.Q.map Φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A') _).mpr hΦq
  haveI hIso3 : IsIso (DerivedCategory.Q.map
      ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫ Φ)) := by
    rw [Functor.map_comp]
    infer_instance
  haveI : (Work.DSG4a.singleZ A).IsKProjective := Work.DSEQ0.singleZ_isKProjective
  have hquot := chainSplitBC.quotient_map_eq_of_Q_map_eq_comp (A := A) (Work.DSG4a.singleZ A) cc q
    ccAn hlift
  haveI hAdd : (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).Additive := by
    unfold Work.DSG4a.baseChangeComplexFunctor
    infer_instance
  have hhom : Homotopy (cc ≫ q) ccAn := HomotopyCategory.homotopyOfEq _ _ hquot
  have hhom' : Homotopy
      ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map (cc ≫ q))
      ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn) :=
    Functor.mapHomotopy (F := ModuleCat.extendScalars (algebraMap A A'))
      (c := ComplexShape.up ℤ) hhom
  have hQ : DerivedCategory.Q.map
        ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map (cc ≫ q)) =
      DerivedCategory.Q.map
        ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn) :=
    Q_map_eq_of_quotient_map_eq (HomotopyCategory.eq_of_homotopy _ _ hhom')
  have hQ2 : DerivedCategory.Q.map
        ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map cc) ≫
        DerivedCategory.Q.map
          ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q) =
      DerivedCategory.Q.map
        ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn) := by
    rw [← Functor.map_comp,
      show (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map cc ≫
          (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q =
        (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map (cc ≫ q) from
        (Functor.map_comp _ _ _).symm, hQ]
  have hgoal : DerivedCategory.Q.map (Work.DSG4a.ccBase P cc ≫
        (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫ Φ) =
      DerivedCategory.Q.map ccAn' := by
    rw [show Work.DSG4a.ccBase P cc ≫
          (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫ Φ =
        Work.DSG4a.eS A A' ≫
          (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map (cc ≫ q) ≫ Φ from by
      simp only [Work.DSG4a.ccBase, Functor.map_comp, Category.assoc]]
    rw [chainSplitBC.cechZ_baseChange_coaug_eq ccAn hccAn ccAn' hccAn' Φ hΦ]
    simp only [Functor.map_comp]
    rw [hQ2]
  have h2 : DerivedCategory.Q.map (Work.DSG4a.ccBase P cc) ≫
        DerivedCategory.Q.map ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫
          Φ) =
      DerivedCategory.Q.map ccAn' := by
    rw [← Functor.map_comp]
    exact hgoal
  have h3 : DerivedCategory.Q.map cc' ≫
        DerivedCategory.Q.map ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫
          Φ) =
      DerivedCategory.Q.map (Work.DSG4a.ccBase P cc) ≫
        DerivedCategory.Q.map ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫
          Φ) := by
    rw [← hlift', h2]
  exact (cancel_mono (DerivedCategory.Q.map
    ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫ Φ))).mp h3

end Work.DSG4a
