import Mathlib
import Submission.Work.DSG1.Basic
import Submission.Work.DSG1.Setup
import Submission.Work.DSG1.injFlasque
import Submission.Work.DSG1.pushforwardFlasque
import Submission.Work.DSG1.unitIsoOfFlasqueM
import Submission.Work.DSG1.rdfpuBridge
import Submission.Work.DSG1.mapSinglePlusComp
import Submission.Work.DSG1.Bookkeep

/-!
# DSG1 (area G1): the comparison map `RΓ(X,𝒪_X) ⟶ RΓ(X',𝒪_{X'})`

Target: `Work.DSG1.comparison`: the existence of
`φ : DSMap.RG A X f ⟶ DSMap.RG A X' (g ≫ f)` with
`DSMap.rgUnit A X f ≫ φ = DSMap.rgUnit A X' (g ≫ f)`
(no properness/separatedness hypotheses are needed).

## The proof

Notation: `F := Γ(X,-) : X.Modules ⥤ ModuleCat A`, `F' := Γ(X',-) = g_* ⋙ F`,
`Q := Scheme.Modules.pushforward g : X'.Modules ⥤ X.Modules`, `loc = DerivedCategory.Plus.Q`,
`Σ_C = DerivedCategory.Plus.singleFunctor C 0`, `S_0 = singlePlusObj`.

* `I' = ι.mapCochainComplexPlus L` is an injective resolution of `𝒪_{X'}` (Mathlib's
  `CochainComplex.Plus.exists_quasiIso_injective`), and `K := Q I'` (degreewise pushforward) is a
  bounded below complex of *flasque* `𝒪_X`-modules: the terms are injective, hence flasque
  (`Work.DSG1.injFlasque`), and pushforward preserves flasqueness (`Work.DSG1.pushforwardFlasque`).
  Hence `u^F_K` is an isomorphism (`Work.DSG1.unitIsoOfFlasqueM`).
* `c' := (mapSinglePlusIso Q 𝒪_{X'}).inv ≫ Q.map i : S_0(Q 𝒪_{X'}) ⟶ K`, and
  `φ := F.rdfp(Σσ) ≫ F.rdfp(spi.hom) ≫ F.rdfp(loc c') ≫ inv(u^F_K) ≫ u^{F'}_{I'} ≫
  F'.rdfp(e.hom)` where `σ = unitToPushforwardObjUnit`.
* Unit compatibility: after rewriting `rgUnit` (`Work.DSG1.rgUnit_eq`) the claim is an identity of
  composites, proved by a diagram chase whose steps are
  + the naturality of the `single`-level unit `rightDerivedFunctorPlusUnit'` at `σ`,
  + the `A`-algebra identity `lin_{X'} = lin_X ≫ Γ(σ)` (`Work.DSG1.linMap_comp_pushforwardUnit`,
    i.e. `Work.DSG1.phi_comp`),
  + `Work.DSG1.rdfpuBridge` at `Q 𝒪_{X'}` and at `𝒪_{X'}` (identifying the `single`-level unit with
    the complex level unit `Functor.rightDerivedFunctorPlusUnit`) and the cancellation
    `spi.inv ≫ spi.hom = 1`,
  + the naturality of the complex level units at `c'` and at `i`,
  + `Work.DSG1.mapSinglePlusComp` (compatibility of `mapSinglePlusIso` with composition),
  + the cancellation `u^F_K ≫ inv u^F_K = 1` and `QIinv.inv ≫ QIinv.hom = 1`.
  Both sides then reduce to `Σ_A(lin_{X'}) ≫ u^{F'}(𝒪_{X'}) = rgUnit A X' (g ≫ f)`.

The commutativity bookkeeping is done with local `let` abbreviations; the tactic
`first | rfl | simp only [Category.assoc]` closes the pure reassociation steps and the remaining
steps are `rw` with the equations above.
-/

namespace Work.DSG1

open CategoryTheory AlgebraicGeometry Limits

universe a b c d

-- The instance searches below (involving `mapCochainComplexPlus` and `InjectiveObject`) are
-- heavy; give them room.
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- (Implementation) The bounded below complex of injective objects underlying an injective
resolution.  Introducing it as a named definition keeps the (heavy) unfolding of
`mapCochainComplexPlus` out of the statement of the lemmas below. -/
noncomputable def resCh {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex.Plus (InjectiveObject C)) : CochainComplex.Plus C :=
  (InjectiveObject.ι C).mapCochainComplexPlus.obj L

lemma resCh_obj_X {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex.Plus (InjectiveObject C)) (n : ℤ) :
    (resCh L).obj.X n = (InjectiveObject.ι C).obj (L.obj.X n) := rfl

lemma resCh_injective {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex.Plus (InjectiveObject C)) (n : ℤ) :
    Injective ((resCh L).obj.X n) := by
  rw [resCh_obj_X]
  infer_instance

/-- (Implementation) The degreewise pushforward of a bounded below complex of `𝒪_{X'}`-modules
along `g : X' ⟶ X`. -/
noncomputable def pushCh {X X' : Scheme.{a}} (g : X' ⟶ X)
    (L : CochainComplex.Plus X'.Modules) : CochainComplex.Plus X.Modules :=
  (Scheme.Modules.pushforward g).mapCochainComplexPlus.obj L

lemma pushCh_obj_X {X X' : Scheme.{a}} (g : X' ⟶ X)
    (L : CochainComplex.Plus X'.Modules) (n : ℤ) :
    (pushCh g L).obj.X n = (Scheme.Modules.pushforward g).obj (L.obj.X n) := rfl

/-- The degreewise pushforward of a complex of injective `𝒪_{X'}`-modules is a complex of
*flasque* `𝒪_X`-modules. -/
lemma pushCh_flasque_terms {X X' : Scheme.{a}} (g : X' ⟶ X)
    (L : CochainComplex.Plus X'.Modules) (hL : ∀ n : ℤ, Injective (L.obj.X n)) :
    ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushCh g L).obj.X n)).obj := by
  intro n
  rw [pushCh_obj_X]
  haveI : Injective (L.obj.X n) := hL n
  exact pushforwardFlasque g (L.obj.X n) (injFlasque (L.obj.X n))

/-- (Implementation) The structure map `𝒪_X ⟶ (Scheme.Modules.pushforward g).obj 𝒪_{X'}`. -/
noncomputable abbrev pushforwardUnitMap {X X' : Scheme.{a}} (g : X' ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom

theorem comparison (A : Type a) [CommRing A] {X X' : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) (g : X' ⟶ X)
    [HasDerivedCategory.{b} (ModuleCat.{a} A)]
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    [HasDerivedCategory.{d} (SheafOfModules X'.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X'.ringCatSheaf)] :
    ∃ φ : DSMap.RG A X f ⟶ DSMap.RG A X' (g ≫ f),
      DSMap.rgUnit A X f ≫ φ = DSMap.rgUnit A X' (g ≫ f) := by
  -- ## 1. An injective resolution `i : (𝒪_{X'})[0] ⟶ I'`.
  haveI hge : (Work.DSG1.singlePlusObj (SheafOfModules X'.ringCatSheaf)
      (SheafOfModules.unit X'.ringCatSheaf)).obj.IsStrictlyGE 0 :=
    inferInstanceAs (((CochainComplex.singleFunctor (SheafOfModules X'.ringCatSheaf) 0).obj
      (SheafOfModules.unit X'.ringCatSheaf)).IsStrictlyGE 0)
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    (Work.DSG1.singlePlusObj (SheafOfModules X'.ringCatSheaf)
      (SheafOfModules.unit X'.ringCatSheaf)) 0
  let I' : CochainComplex.Plus (SheafOfModules X'.ringCatSheaf) := resCh L
  haveI hQi : IsIso ((DerivedCategory.Plus.Q).map i) := Localization.inverts _ _ i hi
  -- ## 2. Push forward to `X`: a bounded below complex `K` of flasque `𝒪_X`-modules.
  let K : CochainComplex.Plus (SheafOfModules X.ringCatSheaf) := pushCh g I'
  have hKfl : ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (K.obj.X n)).obj :=
    pushCh_flasque_terms g I' (fun n => resCh_injective L n)
  -- ## 3. `unitIsoOfFlasque`: `Q (Γ_X K) ≅ R⁺Γ_X (Q K)`.
  haveI hKiso : IsIso ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K) :=
    unitIsoOfFlasqueM A f K hKfl
  -- ## 4. The comparison map.  `φ` is the composite
  -- `F.rdfp(Σσ) ≫ F.rdfp(spi.hom) ≫ F.rdfp(Q c') ≫ inv(u^F_K) ≫ u^{F'}_{I'} ≫ F'.rdfp(e.hom)`,
  -- written in the *decomposed* form (using the functoriality of `F.rdfp` and of `Q`), which is
  -- definitionally the same map but keeps the individual factors visible for the diagram chase.

  let c' : Work.DSG1.singlePlusObj (SheafOfModules X.ringCatSheaf)
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)) ⟶ K :=
    (Work.DSG1.mapSinglePlusIso (Scheme.Modules.pushforward g)
        (SheafOfModules.unit X'.ringCatSheaf)).inv ≫
      (Scheme.Modules.pushforward g).mapCochainComplexPlus.map i
  let QIinv : (DerivedCategory.Plus.Q).obj I' ≅
      (DerivedCategory.Plus.Q).obj (Work.DSG1.singlePlusObj (SheafOfModules X'.ringCatSheaf)
        (SheafOfModules.unit X'.ringCatSheaf)) :=
    (asIso ((DerivedCategory.Plus.Q).map i)).symm
  let SPI : (DerivedCategory.Plus.Q).obj (Work.DSG1.singlePlusObj
        (SheafOfModules X'.ringCatSheaf) (SheafOfModules.unit X'.ringCatSheaf)) ≅
      (DerivedCategory.Plus.singleFunctor (SheafOfModules X'.ringCatSheaf) 0).obj
        (SheafOfModules.unit X'.ringCatSheaf) :=
    Work.DSG1.singlePlusIso (SheafOfModules X'.ringCatSheaf)
      (SheafOfModules.unit X'.ringCatSheaf)
  refine ⟨(DSMap.GammaA A X f).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor (SheafOfModules X.ringCatSheaf) 0).map
          (pushforwardUnitMap g)) ≫
      (DSMap.GammaA A X f).rightDerivedFunctorPlus.map
        (Work.DSG1.singlePlusIso (SheafOfModules X.ringCatSheaf)
          ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))).hom ≫
      (DSMap.GammaA A X f).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.Q).map c') ≫
      inv ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K) ≫
      (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlusUnit.app I' ≫
      (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlus.map (QIinv.hom ≫ SPI.inv), ?_⟩
  -- ## 5. Unit compatibility.
  rw [rgUnit_eq A f, rgUnit_eq A (g ≫ f)]
  -- ### 5.1 abbreviations (all local `let`s: no search, unfolded by `exact`/`rfl`).
  let L := (DerivedCategory.Plus.singleFunctor (ModuleCat.{a} A) 0).map (linMap A f)
  let U := (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit'
      (DSMap.GammaA A X f) 0).app (SheafOfModules.unit X.ringCatSheaf)
  let B1 := Work.DSG1.singlePlusIso (SheafOfModules X.ringCatSheaf)
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))
  let C1 := (DSMap.GammaA A X f).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor (SheafOfModules X.ringCatSheaf) 0).map
        (pushforwardUnitMap g))
  let D1 := (DSMap.GammaA A X f).rightDerivedFunctorPlus.map B1.hom
  let E1 := (DSMap.GammaA A X f).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.Q).map c')
  let V1 := inv ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K)
  let W1 := (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlusUnit.app I'
  let Z1 := (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlus.map (QIinv.hom ≫ SPI.inv)
  let L' := (DerivedCategory.Plus.singleFunctor (ModuleCat.{a} A) 0).map (linMap A (g ≫ f))
  let U' := (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit'
      (DSMap.GammaA A X' (g ≫ f)) 0).app (SheafOfModules.unit X'.ringCatSheaf)
  let R4 := W1 ≫ Z1
  let R3 := V1 ≫ R4
  let R2 := E1 ≫ R3
  let R1 := D1 ≫ R2
  let C2 := (DerivedCategory.Plus.singleFunctor (ModuleCat.{a} A) 0).map
      ((DSMap.GammaA A X f).map (pushforwardUnitMap g))
  let U2 := (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit'
      (DSMap.GammaA A X f) 0).app
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))
  let B2 := (Work.DSG1.singlePlusIso (ModuleCat.{a} A)
      ((DSMap.GammaA A X f).obj ((Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit X'.ringCatSheaf)))).hom
  let C3 := (DerivedCategory.Plus.Q).map
      ((Work.DSG1.mapSinglePlusIso (DSMap.GammaA A X f)
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))).inv)
  let U4 := (DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app
      (Work.DSG1.singlePlusObj (SheafOfModules X.ringCatSheaf)
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)))
  let D2 := (DSMap.GammaA A X f).rightDerivedFunctorPlus.map B1.inv
  let V2 := (DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K
  let Qc := (DerivedCategory.Plus.Q).map
      ((DSMap.GammaA A X f).mapCochainComplexPlus.map c')
  let QY1 := (DerivedCategory.Plus.Q).map
      ((DSMap.GammaA A X f).mapCochainComplexPlus.map
        ((Work.DSG1.mapSinglePlusIso (Scheme.Modules.pushforward g)
          (SheafOfModules.unit X'.ringCatSheaf)).inv))
  let QY2 := (DerivedCategory.Plus.Q).map
      ((DSMap.GammaA A X' (g ≫ f)).mapCochainComplexPlus.map i)
  let QM := (DerivedCategory.Plus.Q).map
      ((Work.DSG1.mapSinglePlusIso (DSMap.GammaA A X' (g ≫ f))
        (SheafOfModules.unit X'.ringCatSheaf)).inv)
  let QM' := (DerivedCategory.Plus.Q).map
      ((DSMap.GammaA A X' (g ≫ f)).mapCochainComplexPlus.map i)
  let UM := (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlusUnit.app
      (Work.DSG1.singlePlusObj (SheafOfModules X'.ringCatSheaf)
        (SheafOfModules.unit X'.ringCatSheaf))
  let ZM := (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.Q).map i)
  let Z2 := (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlus.map SPI.inv
  -- ### 5.2 the moves.
  haveI hAddPd : (Scheme.Modules.pushforward g).Additive := inferInstance
  haveI hAddF : (DSMap.GammaA A X f).Additive := inferInstance
  haveI hAddF' : (DSMap.GammaA A X' (g ≫ f)).Additive := inferInstance
  have nat2 : U ≫ C1 = C2 ≫ U2 :=
    ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit'
      (DSMap.GammaA A X f) 0).naturality (pushforwardUnitMap g)).symm
  have step3 : L ≫ C2 = L' :=
    (Functor.map_comp (DerivedCategory.Plus.singleFunctor (ModuleCat.{a} A) 0)
        (linMap A f) ((DSMap.GammaA A X f).map (pushforwardUnitMap g))).symm.trans
      (congrArg (fun z => (DerivedCategory.Plus.singleFunctor (ModuleCat.{a} A) 0).map z)
        (linMap_comp_pushforwardUnit A f g))
  have step4 : U2 = B2 ≫ C3 ≫ U4 ≫ D2 :=
    rdfpuBridge (DSMap.GammaA A X f)
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))
  have hCanc : D2 ≫ R1 = R2 :=
    Work.DSG1.map_cancel (DSMap.GammaA A X f).rightDerivedFunctorPlus B1 R2
  have step6 : U4 ≫ E1 = Qc ≫ V2 :=
    ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.naturality c').symm
  have hCanV : V2 ≫ V1 ≫ R4 = R4 :=
    Work.DSG1.cancel_hom_inv ((DSMap.GammaA A X f).rightDerivedFunctorPlusUnit.app K) R4
  have hcc : c' = (Work.DSG1.mapSinglePlusIso (Scheme.Modules.pushforward g)
        (SheafOfModules.unit X'.ringCatSheaf)).inv ≫
      (Scheme.Modules.pushforward g).mapCochainComplexPlus.map i := rfl
  have hcc2 : (DSMap.GammaA A X f).mapCochainComplexPlus.map c' =
      (DSMap.GammaA A X f).mapCochainComplexPlus.map
          ((Work.DSG1.mapSinglePlusIso (Scheme.Modules.pushforward g)
            (SheafOfModules.unit X'.ringCatSheaf)).inv) ≫
        (DSMap.GammaA A X f).mapCochainComplexPlus.map
          ((Scheme.Modules.pushforward g).mapCochainComplexPlus.map i) := by
    rw [hcc, Functor.map_comp]
  have h9' : Qc = QY1 ≫ QY2 :=
    ((Functor.map_comp (DerivedCategory.Plus.Q)
        ((DSMap.GammaA A X f).mapCochainComplexPlus.map
          ((Work.DSG1.mapSinglePlusIso (Scheme.Modules.pushforward g)
            (SheafOfModules.unit X'.ringCatSheaf)).inv))
        ((DSMap.GammaA A X f).mapCochainComplexPlus.map
          ((Scheme.Modules.pushforward g).mapCochainComplexPlus.map i))).symm.trans
      (congrArg (DerivedCategory.Plus.Q).map hcc2)).symm
  have step8 : C3 ≫ QY1 = QM :=
    ((Functor.map_comp (DerivedCategory.Plus.Q)
        ((Work.DSG1.mapSinglePlusIso (DSMap.GammaA A X f)
          ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))).inv)
        ((DSMap.GammaA A X f).mapCochainComplexPlus.map
          ((Work.DSG1.mapSinglePlusIso (Scheme.Modules.pushforward g)
            (SheafOfModules.unit X'.ringCatSheaf)).inv))).symm.trans
      (congrArg (DerivedCategory.Plus.Q).map
        (Work.DSG1.mapSinglePlusComp (Scheme.Modules.pushforward g) (DSMap.GammaA A X f)
          (SheafOfModules.unit X'.ringCatSheaf))))
  have step9 : QM' ≫ W1 = UM ≫ ZM :=
    (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlusUnit.naturality i
  have step10 : ZM ≫ Z1 = Z2 :=
    (Functor.map_comp (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlus
        ((DerivedCategory.Plus.Q).map i) (QIinv.hom ≫ SPI.inv)).symm.trans
      (congrArg (DSMap.GammaA A X' (g ≫ f)).rightDerivedFunctorPlus.map
        (Work.DSG1.iso_cancel QIinv SPI.inv))
  have step11 : B2 ≫ QM ≫ UM ≫ Z2 = U' :=
    (rdfpuBridge (DSMap.GammaA A X' (g ≫ f))
      (SheafOfModules.unit X'.ringCatSheaf)).symm
  -- ### 5.3 the chain.
  have hR4u : R4 = W1 ≫ Z1 := rfl
  have hR3u : R3 = V1 ≫ R4 := rfl
  have hR2u : R2 = E1 ≫ R3 := rfl
  have hchain : ((L ≫ U) ≫ (C1 ≫ R1)) = (L' ≫ U') := by
    have h0 : ((L ≫ U) ≫ (C1 ≫ R1)) = (L ≫ ((U ≫ C1) ≫ R1)) := by
      first | rfl | simp only [Category.assoc]
    refine h0.trans ?_
    have h1 : (L ≫ ((U ≫ C1) ≫ R1)) = (L ≫ ((C2 ≫ U2) ≫ R1)) := by
      rw [nat2]
    refine h1.trans ?_
    have h2 : (L ≫ ((C2 ≫ U2) ≫ R1)) = ((L ≫ C2) ≫ (U2 ≫ R1)) := by
      first | rfl | simp only [Category.assoc]
    refine h2.trans ?_
    have h3 : ((L ≫ C2) ≫ (U2 ≫ R1)) = (L' ≫ (U2 ≫ R1)) := by
      rw [step3]
    refine h3.trans ?_
    have h4 : (L' ≫ (U2 ≫ R1)) = (L' ≫ ((B2 ≫ C3 ≫ U4 ≫ D2) ≫ R1)) := by
      rw [step4]
    refine h4.trans ?_
    have h5 : (L' ≫ ((B2 ≫ C3 ≫ U4 ≫ D2) ≫ R1)) =
        (L' ≫ ((B2 ≫ C3 ≫ U4) ≫ (D2 ≫ R1))) := by
      first | rfl | simp only [Category.assoc]
    refine h5.trans ?_
    have h6 : (L' ≫ ((B2 ≫ C3 ≫ U4) ≫ (D2 ≫ R1))) =
        (L' ≫ ((B2 ≫ C3 ≫ U4) ≫ R2)) := by
      rw [hCanc]
    refine h6.trans ?_
    have h7 : (L' ≫ ((B2 ≫ C3 ≫ U4) ≫ R2)) =
        (L' ≫ ((B2 ≫ C3) ≫ ((U4 ≫ E1) ≫ R3))) := by
      rw [hR2u]
      first | rfl | simp only [Category.assoc]
    refine h7.trans ?_
    have h8 : (L' ≫ ((B2 ≫ C3) ≫ ((U4 ≫ E1) ≫ R3))) =
        (L' ≫ ((B2 ≫ C3) ≫ ((Qc ≫ V2) ≫ R3))) := by
      rw [step6]
    refine h8.trans ?_
    have h9 : (L' ≫ ((B2 ≫ C3) ≫ ((Qc ≫ V2) ≫ R3))) =
        (L' ≫ ((B2 ≫ C3) ≫ (Qc ≫ (V2 ≫ R3)))) := by
      first | rfl | simp only [Category.assoc]
    refine h9.trans ?_
    have h10 : (L' ≫ ((B2 ≫ C3) ≫ (Qc ≫ (V2 ≫ R3)))) =
        (L' ≫ ((B2 ≫ C3) ≫ (Qc ≫ R4))) := by
      rw [hR3u, hCanV]
    refine h10.trans ?_
    have h11 : (L' ≫ ((B2 ≫ C3) ≫ (Qc ≫ R4))) =
        (L' ≫ ((B2 ≫ C3) ≫ ((QY1 ≫ QY2) ≫ R4))) := by
      rw [h9']
    refine h11.trans ?_
    have h12 : (L' ≫ ((B2 ≫ C3) ≫ ((QY1 ≫ QY2) ≫ R4))) =
        (L' ≫ (B2 ≫ ((C3 ≫ QY1) ≫ (QY2 ≫ R4)))) := by
      first | rfl | simp only [Category.assoc]
    refine h12.trans ?_
    have h13 : (L' ≫ (B2 ≫ ((C3 ≫ QY1) ≫ (QY2 ≫ R4)))) =
        (L' ≫ (B2 ≫ (QM ≫ (QY2 ≫ R4)))) := by
      rw [step8]
    refine h13.trans ?_
    have h15 : (L' ≫ (B2 ≫ (QM ≫ (QM' ≫ R4)))) =
        (L' ≫ (B2 ≫ (QM ≫ ((QM' ≫ W1) ≫ Z1)))) := by
      rw [hR4u]
      first | rfl | simp only [Category.assoc]
    refine h15.trans ?_
    have h16 : (L' ≫ (B2 ≫ (QM ≫ ((QM' ≫ W1) ≫ Z1)))) =
        (L' ≫ (B2 ≫ (QM ≫ ((UM ≫ ZM) ≫ Z1)))) := by
      rw [step9]
    refine h16.trans ?_
    have h17 : (L' ≫ (B2 ≫ (QM ≫ ((UM ≫ ZM) ≫ Z1)))) =
        (L' ≫ (B2 ≫ (QM ≫ (UM ≫ (ZM ≫ Z1))))) := by
      first | rfl | simp only [Category.assoc]
    refine h17.trans ?_
    have h18 : (L' ≫ (B2 ≫ (QM ≫ (UM ≫ (ZM ≫ Z1))))) =
        (L' ≫ (B2 ≫ (QM ≫ (UM ≫ Z2)))) := by
      rw [step10]
    refine h18.trans ?_
    have h19 : (L' ≫ (B2 ≫ (QM ≫ (UM ≫ Z2)))) = (L' ≫ U') := by
      rw [step11]
    exact h19
  exact hchain

end Work.DSG1
