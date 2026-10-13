import Mathlib
import Submission.Work.DSMap.Map

namespace Work.DSF1.Cech

open CategoryTheory AlgebraicGeometry Limits

set_option backward.isDefEq.respectTransparency false

universe u u' v w

/-- The coaugmentation of the Čech complex of a presheaf along a family `U` is a cycle:
the alternating sum of cofaces kills a constant section. -/
lemma cechComplex_coaug_δ_eq {C : Type u} [Category* C] [HasFiniteProducts C]
    {A : Type u'} [Category* A] [Preadditive A] [HasProducts.{w} A]
    (P : Cᵒᵖ ⥤ A) {T : C} (hT : IsTerminal T) {ι : Type w} (U : ι → C) (i : Fin 2) :
    Pi.lift (fun x : Fin 1 → ι => P.map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫
        (CosimplicialObject.δ ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.cech (FormalCoproduct.mk ι U))).obj P)) i
      = Pi.lift (fun y : Fin 2 → ι => P.map ((hT.from (∏ᶜ (U ∘ y))).op)) := by
  let E := FormalCoproduct.cech (FormalCoproduct.mk ι U)
  let Y := (FormalCoproduct.cosimplicialObjectFunctor E).obj P
  apply Pi.hom_ext (f := fun y : Fin 2 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ y))))
  intro y
  have hR : Pi.lift (fun y : Fin 2 → ι => P.map ((hT.from (∏ᶜ (U ∘ y))).op)) ≫
      Pi.π (fun y : Fin 2 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ y)))) y
      = P.map ((hT.from (∏ᶜ (U ∘ y))).op) :=
    Pi.lift_comp_π _ _
  have hC : Pi.lift (fun x : Fin 1 → ι => P.map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫
      Pi.π (fun x : Fin 1 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ x))))
        ((E.rightOp.map (SimplexCategory.δ i)).unop.f y)
      = P.map ((hT.from (∏ᶜ (U ∘ ((E.rightOp.map (SimplexCategory.δ i)).unop.f y)))).op) :=
    Pi.lift_comp_π _ _
  have hδ : (Y.δ i) ≫ Pi.π (fun y : Fin 2 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ y)))) y
      = Pi.π (fun x : Fin 1 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ x))))
          ((E.rightOp.map (SimplexCategory.δ i)).unop.f y) ≫
        P.map (((E.rightOp.map (SimplexCategory.δ i)).unop.φ y).op) := by
    show (Pi.lift (fun y' : Fin 2 → ι =>
        Pi.π (fun x : Fin 1 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ x))))
          ((E.rightOp.map (SimplexCategory.δ i)).unop.f y') ≫
        P.map (((E.rightOp.map (SimplexCategory.δ i)).unop.φ y').op)) ≫
        Pi.π (fun y : Fin 2 → ι => P.obj (Opposite.op (∏ᶜ (U ∘ y)))) y = _)
    exact Pi.lift_comp_π _ _
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m =>
    Pi.lift (fun x : Fin 1 → ι => P.map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫ m) hδ) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m =>
    m ≫ P.map (((E.rightOp.map (SimplexCategory.δ i)).unop.φ y).op)) hC) ?_
  refine Eq.trans ?_ hR.symm
  rw [← P.map_comp, ← op_comp]
  exact congrArg P.map (congrArg Quiver.Hom.op (hT.hom_ext _ _))

/-- The coaugmentation of the Čech complex of a presheaf along a family `U` is a cycle. -/
lemma cechComplex_coaug_isCycle {C : Type u} [Category* C] [HasFiniteProducts C]
    {A : Type u'} [Category* A] [Preadditive A] [HasProducts.{w} A]
    (P : Cᵒᵖ ⥤ A) {T : C} (hT : IsTerminal T) {ι : Type w} (U : ι → C) :
    Pi.lift (fun x : Fin 1 → ι => P.map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫
      ((cechComplexFunctor U).obj P).d 0 1 = 0 := by
  let E := FormalCoproduct.cech (FormalCoproduct.mk ι U)
  let Y := (FormalCoproduct.cosimplicialObjectFunctor E).obj P
  have hd : ((cechComplexFunctor U).obj P).d 0 1
      = ∑ i : Fin 2, (-1 : ℤ) ^ ((i : ℕ)) • (CosimplicialObject.δ Y) i :=
    (CochainComplex.of_d (fun n => Y.obj (SimplexCategory.mk n))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD Y) 0).trans rfl
  rw [hd, Fin.sum_univ_two, Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 from by norm_num,
    show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 from by norm_num, one_zsmul, neg_zsmul, one_zsmul]
  rw [show Pi.lift (fun x : Fin 1 → ι => P.map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫
        (CosimplicialObject.δ Y) (1 : Fin 2)
      = Pi.lift (fun y : Fin 2 → ι => P.map ((hT.from (∏ᶜ (U ∘ y))).op)) from
        cechComplex_coaug_δ_eq P hT U 1,
    show Pi.lift (fun x : Fin 1 → ι => P.map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫
        (CosimplicialObject.δ Y) (0 : Fin 2)
      = Pi.lift (fun y : Fin 2 → ι => P.map ((hT.from (∏ᶜ (U ∘ y))).op)) from
        cechComplex_coaug_δ_eq P hT U 0,
    add_neg_cancel]

/-- `Pi.lift` is natural in the source variable. -/
lemma piLift_comp {C : Type u} [Category* C] {β : Type v} {F : β → C} [HasProduct F]
    {P₀ Q : C} (a : P₀ ⟶ Q) (p : ∀ b, Q ⟶ F b) :
    Pi.lift (fun b => a ≫ p b) = a ≫ Pi.lift p := by
  apply Pi.hom_ext (f := F)
  intro b
  rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π]

/-- The degree-`0` product of the Čech cochain complex, as an explicit family. -/
noncomputable abbrev cechCoh0 (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (Fin 1 → ι) → ModuleCat.{u} A :=
  fun x => (DSMap.cechPresheaf A X f).obj (Opposite.op (∏ᶜ (U ∘ x)))

/-- The degree-`1` product of the Čech cochain complex, as an explicit family. -/
noncomputable abbrev cechCoh1 (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (Fin 2 → ι) → ModuleCat.{u} A :=
  fun x => (DSMap.cechPresheaf A X f).obj (Opposite.op (∏ᶜ (U ∘ x)))

/-- The Čech coaugmentation of `𝒪_X` (`DSMap.coaug0`) is a cycle. -/
lemma coaug0_cech_d (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    DSMap.coaug0 A X f U ≫ (DSMap.cech A X f U).d 0 1 = 0 := by
  have hT : IsTerminal (⊤ : X.Opens) := isTerminalTop
  have hgen := cechComplex_coaug_isCycle (DSMap.cechPresheaf A X f) hT U
  have hgen' : Pi.lift (f := cechCoh0 A X f U)
        (fun x => (DSMap.cechPresheaf A X f).map ((hT.from (∏ᶜ (U ∘ x))).op)) ≫
      (DSMap.cech A X f U).d 0 1 = 0 := hgen
  have hB : Pi.lift (f := cechCoh0 A X f U)
        (fun x => (DSMap.cechPresheaf A X f).map (homOfLE le_top).op)
      = Pi.lift (f := cechCoh0 A X f U)
        (fun x => (DSMap.cechPresheaf A X f).map ((hT.from (∏ᶜ (U ∘ x))).op)) := by
    apply Pi.hom_ext (f := cechCoh0 A X f U)
    intro x
    rw [Pi.lift_comp_π, Pi.lift_comp_π]
    exact congrArg (fun m => (DSMap.cechPresheaf A X f).map m.op) (hT.hom_ext _ _)
  have hstep : Pi.lift (f := cechCoh0 A X f U)
        (fun x => (DSMap.cechPresheaf A X f).map (homOfLE le_top).op) ≫
      (DSMap.cech A X f U).d 0 1 = 0 := by
    rw [hB, hgen']
  have hA : DSMap.coaug0 A X f U = DSMap.unitTop A X f ≫
      Pi.lift (f := cechCoh0 A X f U)
        (fun x => (DSMap.cechPresheaf A X f).map (homOfLE le_top).op) :=
    (show DSMap.coaug0 A X f U = Pi.lift (f := cechCoh0 A X f U)
        (fun x => DSMap.unitTop A X f ≫ (DSMap.cechPresheaf A X f).map (homOfLE le_top).op)
      from rfl).trans
      (piLift_comp (DSMap.unitTop A X f)
        (fun x => (DSMap.cechPresheaf A X f).map (homOfLE le_top).op))
  calc DSMap.coaug0 A X f U ≫ (DSMap.cech A X f U).d 0 1
      = (DSMap.unitTop A X f ≫ Pi.lift (f := cechCoh0 A X f U)
          (fun x => (DSMap.cechPresheaf A X f).map (homOfLE le_top).op)) ≫
        (DSMap.cech A X f U).d 0 1 := by rw [hA]
    _ = DSMap.unitTop A X f ≫ (Pi.lift (f := cechCoh0 A X f U)
          (fun x => (DSMap.cechPresheaf A X f).map (homOfLE le_top).op) ≫
        (DSMap.cech A X f U).d 0 1) := Category.assoc _ _ _
    _ = DSMap.unitTop A X f ≫ 0 := by rw [hstep]
    _ = 0 := comp_zero

theorem exists_cechZ_lift (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    ∃ cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A) ⟶ DSMap.cechZ A X f U,
      CategoryTheory.CategoryStruct.comp (cc.f 0)
        ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
      CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom
        (DSMap.coaug0 A X f U) := by
  set g₀ := (DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl with hg₀
  set g₁ := (DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl with hg₁
  have hcyc : ∀ k : ℤ, (ComplexShape.up ℤ).Rel 0 k →
      (DSMap.coaug0 A X f U ≫ g₀.inv) ≫ (DSMap.cechZ A X f U).d 0 k = 0 := by
    intro k hk
    have hk' : (0 : ℤ) + 1 = k := hk
    obtain rfl : k = 1 := by rw [← hk']; norm_num
    have hd : (DSMap.cechZ A X f U).d 0 1 = g₀.hom ≫ (DSMap.cech A X f U).d 0 1 ≫ g₁.inv :=
      HomologicalComplex.extend_d_eq (DSMap.cech A X f U) ComplexShape.embeddingUpNat rfl rfl
    have h1 : (DSMap.coaug0 A X f U ≫ g₀.inv) ≫
          (g₀.hom ≫ ((DSMap.cech A X f U).d 0 1 ≫ g₁.inv))
        = DSMap.coaug0 A X f U ≫ ((DSMap.cech A X f U).d 0 1 ≫ g₁.inv) :=
      (Category.assoc _ _ _).trans (congrArg (fun m => DSMap.coaug0 A X f U ≫ m)
        (Iso.inv_hom_id_assoc g₀ ((DSMap.cech A X f U).d 0 1 ≫ g₁.inv)))
    rw [hd, h1, ← Category.assoc, coaug0_cech_d, zero_comp]
  refine ⟨HomologicalComplex.mkHomFromSingle (DSMap.coaug0 A X f U ≫ g₀.inv) hcyc, ?_⟩
  have hcc : (HomologicalComplex.mkHomFromSingle (DSMap.coaug0 A X f U ≫ g₀.inv) hcyc).f 0
      = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        (DSMap.coaug0 A X f U ≫ g₀.inv) :=
    HomologicalComplex.mkHomFromSingle_f (DSMap.coaug0 A X f U ≫ g₀.inv) hcyc
  rw [hcc]
  have h2 : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        (DSMap.coaug0 A X f U ≫ g₀.inv)) ≫ g₀.hom
      = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        DSMap.coaug0 A X f U := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun m =>
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫ m)
      (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun m =>
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫ m)
      (congrArg (fun m => DSMap.coaug0 A X f U ≫ m) (Iso.inv_hom_id g₀))) ?_
    exact congrArg (fun m =>
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫ m)
      (Category.comp_id (DSMap.coaug0 A X f U))
  exact h2

end Work.DSF1.Cech
