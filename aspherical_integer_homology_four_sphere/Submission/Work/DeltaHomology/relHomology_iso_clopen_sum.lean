import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.HomologyBiprod
import Submission.Work.Homology.SingHomologyClopen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology

noncomputable section

/-! ## Cokernels commute with binary biproducts -/

/-- `biprod.map u v` followed by `biprod.desc s t`. -/
lemma biprod_map_desc {C : Type*} [Category C] [Preadditive C] {X1 X2 Y1 Y2 W : C}
    [HasBinaryBiproduct X1 X2] [HasBinaryBiproduct Y1 Y2]
    (u : X1 ⟶ Y1) (v : X2 ⟶ Y2) (s : Y1 ⟶ W) (t : Y2 ⟶ W) :
    biprod.map u v ≫ biprod.desc s t = biprod.desc (u ≫ s) (v ≫ t) := by
  apply biprod.ext_from_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc, biprod.inr_desc]

/-- `biprod.desc s t` followed by a morphism `f`. -/
lemma biprod_desc_comp {C : Type*} [Category C] [Preadditive C] {X Y Z W : C}
    [HasBinaryBiproduct X Y] (s : X ⟶ Z) (t : Y ⟶ Z) (f : Z ⟶ W) :
    biprod.desc s t ≫ f = biprod.desc (s ≫ f) (t ≫ f) := by
  apply biprod.ext_from_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [← Category.assoc, biprod.inl_desc, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_desc, biprod.inr_desc]

/-- **The cokernel of a biproduct of maps is the biproduct of the cokernels.** -/
theorem cokernel_biprod_map_iso {C : Type*} [Category C] [Abelian C]
    {X1 Y1 X2 Y2 : C} (f : X1 ⟶ Y1) (g : X2 ⟶ Y2) :
    Nonempty (cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g) := by
  let c : Y1 ⊞ Y2 ⟶ cokernel f ⊞ cokernel g :=
    biprod.desc (cokernel.π f ≫ biprod.inl) (cokernel.π g ≫ biprod.inr)
  have hzero : biprod.map f g ≫ c = 0 := by
    apply biprod.ext_from_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, biprod.inl_map, Category.assoc]
      dsimp only [c]
      rw [biprod.inl_desc, ← Category.assoc, cokernel.condition]
      simp
    · rw [← Category.assoc, biprod.inr_map, Category.assoc]
      dsimp only [c]
      rw [biprod.inr_desc, ← Category.assoc, cokernel.condition]
      simp
  let a : cokernel f ⟶ cokernel (biprod.map f g) :=
    cokernel.desc f (biprod.inl ≫ cokernel.π (biprod.map f g)) (by
      rw [← Category.assoc, ← biprod.inl_map, Category.assoc, cokernel.condition]
      simp)
  let b : cokernel g ⟶ cokernel (biprod.map f g) :=
    cokernel.desc g (biprod.inr ≫ cokernel.π (biprod.map f g)) (by
      rw [← Category.assoc, ← biprod.inr_map, Category.assoc, cokernel.condition]
      simp)
  have ha : cokernel.π f ≫ a = biprod.inl ≫ cokernel.π (biprod.map f g) :=
    cokernel.π_desc _ _ _
  have hb : cokernel.π g ≫ b = biprod.inr ≫ cokernel.π (biprod.map f g) :=
    cokernel.π_desc _ _ _
  let r := cokernel.desc (biprod.map f g) c hzero
  have hcinl : biprod.inl ≫ c = cokernel.π f ≫ biprod.inl := by
    dsimp only [c]; rw [biprod.inl_desc]
  have hcinr : biprod.inr ≫ c = cokernel.π g ≫ biprod.inr := by
    dsimp only [c]; rw [biprod.inr_desc]
  have hcl : c ≫ biprod.desc a b = cokernel.π (biprod.map f g) := by
    apply biprod.ext_from_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, hcinl, Category.assoc, biprod.inl_desc, ha]
    · rw [← Category.assoc, hcinr, Category.assoc, biprod.inr_desc, hb]
  have hpr : cokernel.π (biprod.map f g) ≫ r = c := by
    dsimp only [r]; rw [cokernel.π_desc]
  have har : a ≫ r = biprod.inl := by
    apply (cancel_epi (cokernel.π f)).1
    rw [← Category.assoc, ha, Category.assoc, hpr, hcinl]
  have hbr : b ≫ r = biprod.inr := by
    apply (cancel_epi (cokernel.π g)).1
    rw [← Category.assoc, hb, Category.assoc, hpr, hcinr]
  refine ⟨{ hom := r, inv := biprod.desc a b, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply (cancel_epi (cokernel.π (biprod.map f g))).1
    rw [← Category.assoc, hpr, hcl, Category.comp_id]
  · apply biprod.ext_from_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, biprod.inl_desc, har, Category.comp_id]
    · rw [← Category.assoc, biprod.inr_desc, hbr, Category.comp_id]

/-! ## Chain-level invariance and decomposition -/

/-- A homeomorphism of topological spaces induces an isomorphism of singular
chain complexes. -/
def chainHomeoIso (R : ModuleCat ℤ) {α β : Type} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) :
    singChain R (TopCat.of α) ≅ singChain R (TopCat.of β) where
  hom := singChainMap R (homeomorphTopCatHom e)
  inv := singChainMap R (homeomorphTopCatInv e)
  hom_inv_id := by rw [← singChainMap_comp, homeomorphTopCatHom_comp_inv, singChainMap_id]
  inv_hom_id := by rw [← singChainMap_comp, homeomorphTopCatInv_comp_hom, singChainMap_id]

lemma chainHomeoIso_inv (R : ModuleCat ℤ) {α β : Type} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) :
    (chainHomeoIso R e).inv = singChainMap R (homeomorphTopCatInv e) := rfl

/-- The clopen decomposition of the singular chain complex, with the inverse
recorded explicitly as the sum of the two inclusions. -/
def clopenChainIso (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) :
    singChain R X ≅ (singChain R (TopCat.of A) ⊞ singChain R (TopCat.of (Aᶜ : Set X))) := by
  have hcomp : ∀ n, IsIso ((biprod.desc (sChainMap R (incl A))
      (sChainMap R (incl (Aᶜ : Set X)))).f n) := by
    intro n
    have hδ : (HomologicalComplex.biprodXIso (sChain R (TopCat.of A))
          (sChain R (TopCat.of (Aᶜ : Set X))) n).inv
        ≫ (biprod.desc (sChainMap R (incl A)) (sChainMap R (incl (Aᶜ : Set X)))).f n
        = biprod.desc ((sChainMap R (incl A)).f n) ((sChainMap R (incl (Aᶜ : Set X))).f n) := by
      apply biprod.hom_ext'
      · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
          HomologicalComplex.biprod_inl_desc_f, biprod.inl_desc]
      · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
          HomologicalComplex.biprod_inr_desc_f, biprod.inr_desc]
    have hIsIso : IsIso (biprod.desc ((sChainMap R (incl A)).f n)
        ((sChainMap R (incl (Aᶜ : Set X))).f n)) :=
      IsIso.mk ⟨beta R X A hA n, desc_comp_beta R X A hA n, beta_comp_desc R X A hA n⟩
    exact IsIso.of_isIso_fac_left hδ
  have hIsIso : IsIso (biprod.desc (sChainMap R (incl A)) (sChainMap R (incl (Aᶜ : Set X)))) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact (asIso (biprod.desc (sChainMap R (incl A)) (sChainMap R (incl (Aᶜ : Set X))))).symm

lemma clopenChainIso_inv (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (hA : IsClopen A) :
    (clopenChainIso R X A hA).inv
      = biprod.desc (inclChain R X A) (inclChain R X (Aᶜ : Set X)) := rfl

/-! ## The homeomorphisms identifying the pieces of the two decompositions -/

/-- `A ∩ P`, viewed inside the space `A`, is canonically homeomorphic to `A ∩ P`
viewed inside the space `P`. -/
def homeoSubtypes1 {X : TopCat} (A P : Set X) :
    (↥{x : ↥A | (x : X) ∈ P}) ≃ₜ (↥{x : ↥P | (x : X) ∈ A}) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- `A ∖ P`, viewed inside the space `A`, is canonically homeomorphic to
`A ∩ Pᶜ` viewed inside the space `Pᶜ`. -/
def homeoSubtypes2 {X : TopCat} (A P : Set X) :
    (↥{x : ↥A | (x : X) ∉ P}) ≃ₜ (↥{x : ↥Pᶜ | (x : X) ∈ A}) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

lemma homeoSubtypes1_comp {X : TopCat} (A P : Set X) :
    homeomorphTopCatInv (homeoSubtypes1 A P) ≫ incl ({x : ↥A | (x : X) ∈ P} : Set ↥A)
        ≫ incl A
      = incl ({x : ↥P | (x : X) ∈ A} : Set ↥P) ≫ incl P := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma homeoSubtypes2_comp {X : TopCat} (A P : Set X) :
    homeomorphTopCatInv (homeoSubtypes2 A P) ≫ incl (({x : ↥A | (x : X) ∈ P} : Set ↥A)ᶜ)
        ≫ incl A
      = incl ({x : ↥Pᶜ | (x : X) ∈ A} : Set ↥Pᶜ) ≫ incl (Pᶜ : Set X) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-! ## The main theorem -/

/-- **Additivity of relative homology over a clopen splitting.** -/
theorem relHomology_iso_clopen_sum {X : TopCat} (A P : Set X) (hP : IsClopen P) (n : ℕ) :
    Nonempty (relHomology ZMod n X A ≅
      relHomology ZMod n (TopCat.of (P : Set X)) {x : ↥(P : Set X) | (x : X) ∈ A} ⊞
      relHomology ZMod n (TopCat.of (Pᶜ : Set X)) {x : ↥(Pᶜ : Set X) | (x : X) ∈ A}) := by
  have hA' : IsClopen ({x : ↥A | (x : X) ∈ P} : Set ↥A) := hP.preimage continuous_subtype_val
  let q : singChain ZMod X ≅
      (singChain ZMod (TopCat.of (P : Set X)) ⊞ singChain ZMod (TopCat.of (Pᶜ : Set X))) :=
    clopenChainIso ZMod X P hP
  let eA : singChain ZMod (TopCat.of (A : Set X)) ≅
      (singChain ZMod (TopCat.of ({x : ↥A | (x : X) ∈ P} : Set ↥A))
        ⊞ singChain ZMod (TopCat.of ↥(({x : ↥A | (x : X) ∈ P} : Set ↥A)ᶜ))) :=
    clopenChainIso ZMod (TopCat.of (A : Set X)) {x : ↥A | (x : X) ∈ P} hA'
  let e1 : singChain ZMod (TopCat.of ({x : ↥A | (x : X) ∈ P} : Set ↥A)) ≅
      singChain ZMod (TopCat.of ({x : ↥P | (x : X) ∈ A} : Set ↥P)) :=
    chainHomeoIso ZMod (homeoSubtypes1 A P)
  let e2 : singChain ZMod (TopCat.of ↥(({x : ↥A | (x : X) ∈ P} : Set ↥A)ᶜ)) ≅
      singChain ZMod (TopCat.of ({x : ↥Pᶜ | (x : X) ∈ A} : Set ↥Pᶜ)) :=
    chainHomeoIso ZMod (homeoSubtypes2 A P)
  let p : singChain ZMod (TopCat.of (A : Set X)) ≅
      (singChain ZMod (TopCat.of ({x : ↥P | (x : X) ∈ A} : Set ↥P))
        ⊞ singChain ZMod (TopCat.of ({x : ↥Pᶜ | (x : X) ∈ A} : Set ↥Pᶜ))) :=
    eA ≪≫ biprod.mapIso e1 e2
  let f1 : singChain ZMod (TopCat.of ({x : ↥P | (x : X) ∈ A} : Set ↥P)) ⟶
      singChain ZMod (TopCat.of (P : Set X)) :=
    inclChain ZMod (TopCat.of (P : Set X)) {x : ↥P | (x : X) ∈ A}
  let f2 : singChain ZMod (TopCat.of ({x : ↥Pᶜ | (x : X) ∈ A} : Set ↥Pᶜ)) ⟶
      singChain ZMod (TopCat.of (Pᶜ : Set X)) :=
    inclChain ZMod (TopCat.of (Pᶜ : Set X)) {x : ↥Pᶜ | (x : X) ∈ A}
  have hp : p.inv = biprod.map e1.inv e2.inv
      ≫ biprod.desc (inclChain ZMod (TopCat.of (A : Set X)) ({x : ↥A | (x : X) ∈ P} : Set ↥A))
          (inclChain ZMod (TopCat.of (A : Set X))
            (({x : ↥A | (x : X) ∈ P} : Set ↥A)ᶜ)) := rfl
  have hq : q.inv = biprod.desc (inclChain ZMod X P) (inclChain ZMod X (Pᶜ : Set X)) := rfl
  have h1 : e1.inv
      ≫ inclChain ZMod (TopCat.of (A : Set X)) ({x : ↥A | (x : X) ∈ P} : Set ↥A)
      ≫ inclChain ZMod X A
      = inclChain ZMod (TopCat.of (P : Set X)) {x : ↥P | (x : X) ∈ A}
      ≫ inclChain ZMod X P := by
    rw [show e1.inv = singChainMap ZMod (homeomorphTopCatInv (homeoSubtypes1 A P)) from rfl]
    rw [← singChainMap_comp, ← singChainMap_comp, ← singChainMap_comp, homeoSubtypes1_comp]
  have h2 : e2.inv
      ≫ inclChain ZMod (TopCat.of (A : Set X)) (({x : ↥A | (x : X) ∈ P} : Set ↥A)ᶜ)
      ≫ inclChain ZMod X A
      = inclChain ZMod (TopCat.of (Pᶜ : Set X)) {x : ↥Pᶜ | (x : X) ∈ A}
      ≫ inclChain ZMod X (Pᶜ : Set X) := by
    rw [show e2.inv = singChainMap ZMod (homeomorphTopCatInv (homeoSubtypes2 A P)) from rfl]
    rw [← singChainMap_comp, ← singChainMap_comp, ← singChainMap_comp, homeoSubtypes2_comp]
  have h : p.inv ≫ inclChain ZMod X A = biprod.map f1 f2 ≫ q.inv := by
    rw [hp, hq, Category.assoc, biprod_desc_comp, biprod_map_desc, biprod_map_desc, h1, h2]
  have w : inclChain ZMod X A ≫ q.hom = p.hom ≫ biprod.map f1 f2 := by
    have key : p.inv ≫ inclChain ZMod X A ≫ q.hom = biprod.map f1 f2 := by
      rw [← Category.assoc, h, Category.assoc, q.inv_hom_id, Category.comp_id]
    rw [← key, ← Category.assoc, p.hom_inv_id, Category.id_comp]
  obtain ⟨eiso⟩ := cokernel_biprod_map_iso f1 f2
  obtain ⟨hb⟩ := HomologyBiprod (cokernel f1) (cokernel f2) n
  refine ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (cokernel.mapIso (inclChain ZMod X A) (biprod.map f1 f2) p q w ≪≫ eiso) ≪≫ hb⟩

end

end Work.DeltaHomology
