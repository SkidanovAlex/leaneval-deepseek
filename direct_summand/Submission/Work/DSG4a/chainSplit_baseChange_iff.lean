import Mathlib
import Submission.Work.DSG4a.Data
import Submission.Work.DSG4a.cechZ_baseChange
import Submission.Work.DSG4a.quasiIso_baseChangeComplexFunctor
import Submission.Work.DSG4a.sub_coaugElem_mem_range_of_Q_map_eq
import Submission.Work.DSG4a.CSB_Main
import Submission.Work.DSG4a.chainSplitBC.sub_coaugElem_mem_range_of_Q_map_eq_aux
import Submission.Work.DSG4a.chainSplitBC.chainSplit_congr_of_sub_mem_range
import Submission.Work.DSG4a.chainSplitBC.chainSplit_ccBase_iff

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct
set_option backward.isDefEq.respectTransparency false
universe u
-- Compatibility of the Cech model with flat base change (the `hbc` input of area G4a).
-- Data: `ccAn`, `ccAn'` are the coaugmentations produced by the area `F1` for a finite affine
-- cover `U` of `X` and for the pulled-back cover of `X' = X x_Spec A Spec A'`; `Φ` is the Cech
-- base-change comparison `Work.DSG4a.cechZ_baseChange` (quasi-isomorphism, carrying the
-- coaugmentation of `cechZ A X f U` to the one of `cechZ A' X' f' U'`); `P` is a K-projective
-- model of `cechZ A X f U` with coaugmentation `cc` (a lift of `ccAn` along `q`), and `cc'` is a
-- coaugmentation of the base-changed model `baseChangeComplex P` lifting `ccAn'` along
-- `q_b = baseChangeComplexFunctor.map q ≫ Φ`.
-- Conclusion: `ChainSplit (baseChangeComplex P) cc'` is equivalent to the unimodularity of the
-- base change `1 ⊗ modelElem P cc` of the model element in `A' ⊗[A] modelModule P`.
-- Recipe:
-- (1) Define `eS : singleZ A' ⟶ (baseChangeComplexFunctor).obj (singleZ A)`, the canonical
--     comparison of the single-object complexes; its degree-0 part is the isomorphism
--     `A' ≅ A' ⊗[A] A` transported through `singleObjXSelf`, and its components in degrees ≠ 0
--     are zero maps between zero objects.
-- (2) Chain-level coherence: `ccAn' = eS ≫ (baseChangeComplexFunctor).map ccAn ≫ Φ`.  Use
--     `coaugClause` at `A` and at `A'` (`HomologicalComplex.Hom.ext`; in degrees ≠ 0 the source
--     is a zero object; in degree 0 evaluate at `1`, where the clauses give `coaugZElem` on both
--     sides, and use the element statement `hΦ`).
-- (3) Put `ccB := eS ≫ (baseChangeComplexFunctor).map cc`.  From `hlift` and the K-projectivity
--     of `singleZ A` (`Work.DSEQ0.singleZ_isKProjective`), `cc ≫ q` is homotopic to `ccAn`
--     (`CochainComplex.IsKProjective.Qh_map_bijective`, `DerivedCategory.quotientCompQhIso`,
--     `HomotopyCategory.homotopyOfEq`; the pattern is in
--     `Work.DSG4a.sub_coaugElem_mem_range_of_Q_map_eq`); `baseChangeComplexFunctor` preserves
--     homotopies (`HomologicalComplex.Homotopy.map`), so with (2),
--     `Q.map ccB ≫ Q.map q_b = Q.map ccAn'`.
-- (4) `Q.map q_b` is an isomorphism (`hflat`, `hq` give `QuasiIso (baseChangeComplexFunctor.map q)`;
--     `hΦq` gives `QuasiIso Φ`), so `hlift'` gives `Q.map cc' = Q.map ccB`; hence
--     `coaugElem (baseChangeComplex P) cc'` and `coaugElem (baseChangeComplex P) ccB` differ by an
--     element of `im (d⁻¹)` (`Work.DSG4a.sub_coaugElem_mem_range_of_Q_map_eq`; note that its unused
--     `[P.IsKProjective]` binder would ask for `IsKProjective (baseChangeComplex P)`, so it is
--     easier to inline the `Qh_map_bijective` argument).
-- (5) `coaugElem (baseChangeComplex P) ccB = 1 ⊗ coaugElem P cc` (computation with `eS` and
--     `singleObjXSelf`).
-- (6) `ChainSplit C c` is `∃ s, s ∘ d = 0 ∧ s x = 1`, which is unchanged by adding an element of
--     `im (d⁻¹)` to `x`; and `A' ⊗[A] (P.X 0 ⧸ im d) ≅ (A' ⊗[A] P.X 0) ⧸ im (A' ⊗ d)` is
--     `TensorProduct.tensorQuotientEquiv` (AlgebraTensorModule version), carrying `1 ⊗ [x]` to the
--     class of `1 ⊗ x`.  Conclude with `Work.DSG4a.chainSplit_iff_isUnimodular` and
--     `Work.DSG4a.isUnimodular_apply_iff`.
theorem chainSplit_baseChange_iff {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} A')]
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
    (hccAn' : Work.DSG4a.coaugClause (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
      (fun i => Work.DSG4a.baseChangeOpen X f (U i)) ccAn')
    (Φ : Work.DSG4a.baseChangeComplex (A := A) (A' := A') (DSMap.cechZ A X f U) ⟶
      DSMap.cechZ A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
        (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (hΦq : QuasiIso Φ)
    (hΦ : ∀ a' : A', (Φ.f 0) (a' ⊗ₜ[A, algebraMap A A'] Work.DSG4a.coaugZElem A X f U) =
      a' • Work.DSG4a.coaugZElem A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
        (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (cc' : Work.DSG4a.singleZ A' ⟶ Work.DSG4a.baseChangeComplex (A := A) (A' := A') P)
    (hlift' : DerivedCategory.Q.map ccAn' = DerivedCategory.Q.map cc' ≫
      DerivedCategory.Q.map ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map q ≫ Φ)) :
    Work.DSG4a.Criterion.ChainSplit (Work.DSG4a.baseChangeComplex (A := A) (A' := A') P) cc' ↔
      Module.IsUnimodular A' (TensorProduct.mk A A' (Work.DSG4a.Criterion.modelModule P) 1
        (Work.DSG4a.Criterion.modelElem P cc)) := by
  have hQ : DerivedCategory.Q.map cc' = DerivedCategory.Q.map (Work.DSG4a.ccBase P cc) :=
    Work.DSG4a.Q_map_ccBase X f U hU hflat P q hq cc ccAn hccAn hlift ccAn' hccAn' Φ hΦq hΦ
      cc' hlift'
  have hmem := Work.DSG4a.chainSplitBC.sub_coaugElem_mem_range_of_Q_map_eq_aux (A := A')
    (Work.DSG4a.baseChangeComplex (A := A) (A' := A') P) cc'
    (Work.DSG4a.ccBase P cc) hQ
  exact (Work.DSG4a.chainSplitBC.chainSplit_congr_of_sub_mem_range (A := A')
    (Work.DSG4a.baseChangeComplex (A := A) (A' := A') P) cc' (Work.DSG4a.ccBase P cc)
    hmem).trans (Work.DSG4a.chainSplitBC.chainSplit_ccBase_iff P cc)

end Work.DSG4a
