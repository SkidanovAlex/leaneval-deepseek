import Mathlib
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.thomClass_of_cover_gen
import Submission.Work.Thom.nonempty_thomClass_of_compatible_local
import Submission.Work.Thom.transgressionSameSpace
import Submission.Work.Thom.transgressionNatural
import Submission.Work.Thom.transgressionPiAux
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Work.TangentClasses
open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

open Work.Thom (relCohMap relPb relToAbs mixedCupC Coh CohMap pdCohIso subtypeMap)

noncomputable section

/-! ## The canonical homeomorphism `↥T ≅ (Subtype.val)⁻¹T ⊆ ↥S` -/

noncomputable def luSubHomeo {X : Type} [TopologicalSpace X] {S T : Set X} (hTS : T ⊆ S) :
    ↥T ≃ₜ ↥((Subtype.val : ↥S → X) ⁻¹' T) :=
  TopCat.homeoOfIso (HMV.subSubIso (X := TopCat.of X) hTS)

@[simp] theorem luSubHomeo_apply {X : Type} [TopologicalSpace X] {S T : Set X} (hTS : T ⊆ S)
    (x : ↥T) : (((luSubHomeo hTS) x : ↥S) : X) = (x : X) := rfl

@[simp] theorem luSubHomeo_symm_apply {X : Type} [TopologicalSpace X] {S T : Set X} (hTS : T ⊆ S)
    (y : ↥((Subtype.val : ↥S → X) ⁻¹' T)) :
    (((luSubHomeo hTS).symm y : ↥T) : X) = (y : X) := rfl

theorem luHbf {X : TopCat} (A : Set X) {S T : Set X} (hTS : T ⊆ S)
    (y : ↥((Subtype.val : ↥S → X) ⁻¹' T)) (hy : ((y : ↥S) : X) ∈ A) :
    (((luSubHomeo hTS).symm y : ↥T) : X) ∈ A := hy

/-- The transport map of `pdCohSub` along a subset inclusion. -/
noncomputable def luHom (X : TopCat) (A : Set X) {S T : Set X} (hTS : T ⊆ S) (k : ℕ) :
    pdCohSub X A T k ⟶ pdCohSub (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A)
      ((Subtype.val : ↥S → X) ⁻¹' T) k :=
  let φ : ↥T ≃ₜ ↥((Subtype.val : ↥S → X) ⁻¹' T) := luSubHomeo hTS
  Work.Thom.relCohMap (φ.symm : C(↥((Subtype.val : ↥S → X) ⁻¹' T), ↥T))
    (interAU (X := TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A) ((Subtype.val : ↥S → X) ⁻¹' T))
    (interAU A T)
    (fun y hy => luHbf A hTS y hy) ℤ k

theorem luHom_isIso (X : TopCat) (A : Set X) {S T : Set X} (hTS : T ⊆ S) (k : ℕ) :
    IsIso (luHom X A hTS k) := by
  rw [isIso_iff_mono_and_epi]
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    (interAU (X := TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A) ((Subtype.val : ↥S → X) ⁻¹' T))
    (interAU A T) (luSubHomeo hTS).symm
    (fun y => ⟨fun hy => luHbf A hTS y hy, fun hy => by
      show ((y : ↥S) : X) ∈ A
      rw [show ((y : ↥S) : X) = (((luSubHomeo hTS).symm y : ↥T) : X) from rfl]
      exact hy⟩) ℤ k
  exact ⟨(ModuleCat.mono_iff_injective _).mpr hbij.1,
    (ModuleCat.epi_iff_surjective _).mpr hbij.2⟩

/-- The transport isomorphism of `pdCohSub` along a subset inclusion. -/
noncomputable def luIso (X : TopCat) (A : Set X) {S T : Set X} (hTS : T ⊆ S) (k : ℕ) :
    pdCohSub X A T k ≅ pdCohSub (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A)
      ((Subtype.val : ↥S → X) ⁻¹' T) k :=
  @asIso _ _ _ _ (luHom X A hTS k) (luHom_isIso X A hTS k)

theorem luIso_hom (X : TopCat) (A : Set X) {S T : Set X} (hTS : T ⊆ S) (k : ℕ) :
    (luIso X A hTS k).hom = luHom X A hTS k := rfl

/-! ## Rewriting `pdCohMap` / `pdCohRes` as `relCohMap` -/

@[simp] theorem pdCohMap_eq_relCohMap (X : TopCat) (A U W : Set X) (hWU : W ⊆ U) (k : ℕ) :
    pdCohMap X A U W hWU k = Work.Thom.relCohMap (TopCat.Hom.hom (pdIncl U W hWU))
      (interAU A W) (interAU A U) (fun _ hy => hy) ℤ k := rfl

@[simp] theorem pdCohRes_eq_relCohMap (X : TopCat) (A U : Set X) (k : ℕ) :
    pdCohRes X A U k = Work.Thom.relCohMap (Work.Thom.subtypeMap U)
      (interAU A U) A (fun _ hy => hy) ℤ k := rfl

/-- Composition of `relCohMap`s. -/
theorem luRelCohMap_comp {X₀ X₁ X₂ : Type} [TopologicalSpace X₀] [TopologicalSpace X₁]
    [TopologicalSpace X₂] (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂) (f : C(X₀, X₁)) (g : C(X₁, X₂))
    (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) (k : ℕ) :
    Work.Thom.relCohMap g A₁ A₂ hg ℤ k ≫ Work.Thom.relCohMap f A₀ A₁ hf ℤ k
      = Work.Thom.relCohMap (g.comp f) A₀ A₂ (fun x hx => hg (f x) (hf x hx)) ℤ k :=
  Work.Thom.relCohMap_compA A₀ A₁ A₂ f g hf hg _ ℤ k

/-- **Naturality of the transport iso with respect to restriction to a smaller piece.** -/
theorem luIso_natural (X : TopCat) (A : Set X) {S T T' : Set X} (hTS : T ⊆ S)
    (hT'S : T' ⊆ S) (hT'T : T' ⊆ T) (k : ℕ) :
    (luIso X A hTS k).hom ≫ pdCohMap (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A)
        ((Subtype.val : ↥S → X) ⁻¹' T) ((Subtype.val : ↥S → X) ⁻¹' T')
        (Set.preimage_mono hT'T) k
      = pdCohMap X A T T' hT'T k ≫ (luIso X A hT'S k).hom := by
  rw [luIso_hom, luIso_hom, luHom, luHom,
    pdCohMap_eq_relCohMap (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A),
    pdCohMap_eq_relCohMap X A]
  rw [luRelCohMap_comp, luRelCohMap_comp]
  exact Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) _ _ ℤ k

/-- Naturality of `luHom` (the `luIso_hom` form of `luIso_natural`). -/
theorem luHom_natural (X : TopCat) (A : Set X) {S T T' : Set X} (hTS : T ⊆ S)
    (hT'S : T' ⊆ S) (hT'T : T' ⊆ T) (k : ℕ) :
    luHom X A hTS k ≫ pdCohMap (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A)
        ((Subtype.val : ↥S → X) ⁻¹' T) ((Subtype.val : ↥S → X) ⁻¹' T')
        (Set.preimage_mono hT'T) k
      = pdCohMap X A T T' hT'T k ≫ luHom X A hT'S k :=
  luIso_natural X A hTS hT'S hT'T k

/-- **The restriction of the transport iso**: restricting from `S` to `T` is the same as
restricting inside `↥S` and transporting back. -/
theorem luIso_res (X : TopCat) (A : Set X) {S T : Set X} (hST : T ⊆ S) (k : ℕ) :
    pdCohMap X A S T hST k ≫ (luIso X A hST k).hom
      = pdCohRes (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' A) ((Subtype.val : ↥S → X) ⁻¹' T) k := by
  rw [luIso_hom, luHom, pdCohMap_eq_relCohMap X A, pdCohRes_eq_relCohMap]
  rw [luRelCohMap_comp]
  exact Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) _ _ ℤ k


/-! ## Restriction functoriality -/

/-- Restriction to a smaller piece factors through restriction to a larger one. -/
theorem pdCohRes_comp (X : TopCat) (A U W : Set X) (hWU : W ⊆ U) (k : ℕ) :
    pdCohRes X A W k = pdCohRes X A U k ≫ pdCohMap X A U W hWU k := by
  rw [pdCohRes_eq_relCohMap X A, pdCohRes_eq_relCohMap X A, pdCohMap_eq_relCohMap X A]
  rw [luRelCohMap_comp]
  exact Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) _ _ ℤ k

/-! ## `relCohMap` and `pdCohIso` -/

/-- **The pullback to a space, followed by the comparison `pdCohIso`.** -/
theorem relPb_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (k : ℕ)
    (x : pdCoh (TopCat.of Y) ∅ k) :
    (pdCohIso X k).hom ((relPb f k).hom x) = (CohMap f ℤ k).hom ((pdCohIso Y k).hom x) := by
  have h : (relPb f k) ≫ (pdCohIso X k).hom = (pdCohIso Y k).hom ≫ CohMap f ℤ k := by
    rw [relPb, show (pdCohIso X k).hom = relToAbs ℤ (∅ : Set X) k from rfl,
      show (pdCohIso Y k).hom = relToAbs ℤ (∅ : Set Y) k from rfl]
    exact Work.Thom.relCohMap_relToAbs f (∅ : Set X) (∅ : Set Y) (fun _ h => h) ℤ k
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-! ## The piece projection and the piece cup map -/

/-- The projection of the piece over `U`. -/
noncomputable def luFPiece {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (U : Set X) : C(↥(π ⁻¹' U), ↥U) :=
  ⟨fun p => ⟨π p.1, p.2⟩, (π.continuous.comp continuous_subtype_val).subtype_mk (fun p => p.2)⟩

/-- The base-level cup map of the piece over `U`: `x ↦ π_U^*(x) ⌣ cU`. -/
noncomputable def luCupMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U : Set X}
    (cU : pdCohSub (TopCat.of Y) A (π ⁻¹' U) n) (k : ℕ) :
    Coh ℤ k ↥U →ₗ[ℤ] pdCohSub (TopCat.of Y) A (π ⁻¹' U) (k + n) :=
  (LinearMap.applyₗ cU).comp
    ((mixedCupC ℤ (interAU (X := TopCat.of Y) A (π ⁻¹' U)) k n).comp
      (CohMap (luFPiece π U) ℤ k).hom)

/-- The cup map of the piece over `U`, as a morphism of the relative cohomology of the ambient
spaces. -/
noncomputable def luTpiece {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U : Set X}
    (cU : pdCohSub (TopCat.of Y) A (π ⁻¹' U) n) (k : ℕ) :
    pdCohSub (TopCat.of X) ∅ U k ⟶ pdCohSub (TopCat.of Y) A (π ⁻¹' U) (k + n) :=
  relPb (luFPiece π U) k ≫ Work.Thom.TsqH.Ttop (TopCat.of ↥(π ⁻¹' U))
    (interAU (X := TopCat.of Y) A (π ⁻¹' U)) n cU k

/-- The formula for the piece cup map. -/
theorem luTpiece_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U : Set X}
    (cU : pdCohSub (TopCat.of Y) A (π ⁻¹' U) n) (k : ℕ)
    (x : pdCohSub (TopCat.of X) ∅ U k) :
    (luTpiece π A n cU k).hom x = (luCupMap π A n cU k) ((pdCohIso ↥U k).hom x) := by
  rw [luTpiece, ModuleCat.hom_comp, LinearMap.comp_apply]
  show (mixedCupC ℤ (interAU (X := TopCat.of Y) A (π ⁻¹' U)) k n)
      ((pdCohIso ↥(π ⁻¹' U) k).hom ((relPb (luFPiece π U) k).hom x)) cU
    = (luCupMap π A n cU k) ((pdCohIso ↥U k).hom x)
  rw [relPb_apply]
  rfl

/-- The piece cup map is an isomorphism iff the base-level cup map is bijective. -/
theorem luTpiece_isIso_iff {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U : Set X}
    (cU : pdCohSub (TopCat.of Y) A (π ⁻¹' U) n) (k : ℕ) :
    IsIso (luTpiece π A n cU k) ↔ Function.Bijective (luCupMap π A n cU k) := by
  have he : Function.Bijective ⇑(pdCohIso ↥U k).hom :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso (pdCohIso ↥U k).hom
  have hcomp : ⇑(luTpiece π A n cU k).hom
      = (luCupMap π A n cU k) ∘ ⇑(pdCohIso ↥U k).hom := by
    funext x
    rw [Function.comp_apply, luTpiece_apply]
  rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective]
  change Function.Injective ⇑(luTpiece π A n cU k).hom
      ∧ Function.Surjective ⇑(luTpiece π A n cU k).hom ↔ _
  rw [hcomp]
  constructor
  · intro h
    refine ⟨?_, fun b => ?_⟩
    · intro a b hab
      obtain ⟨a₀, rfl⟩ := he.2 a
      obtain ⟨b₀, rfl⟩ := he.2 b
      have h2 : ((luCupMap π A n cU k) ∘ ⇑(pdCohIso ↥U k).hom) a₀
          = ((luCupMap π A n cU k) ∘ ⇑(pdCohIso ↥U k).hom) b₀ := hab
      rw [h.1 h2]
    · obtain ⟨x, hx⟩ := h.2 b
      exact ⟨⇑(pdCohIso ↥U k).hom x, hx⟩
  · intro h
    exact ⟨h.1.comp he.1, h.2.comp he.2⟩

/-! ## Mayer-Vietoris middle exactness for a subset -/

/-- **The glueing of two piece classes**: two classes over `U` and over `V` which agree on the
overlap are the restrictions of a class over the whole space. -/
theorem lu_exists_glue (X : TopCat) (A : Set X) (n : ℕ) {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (cU : pdCohSub X A U n)
    (cV : pdCohSub X A V n)
    (hUV : (pdCohMap X A U (U ∩ V) Set.inter_subset_left n).hom cU
      = (pdCohMap X A V (U ∩ V) Set.inter_subset_right n).hom cV) :
    ∃ τ : pdCoh X A n, pdCohRes X A U n τ = cU ∧ pdCohRes X A V n τ = cV := by
  classical
  set w : pdCohBiprod X A U V n :=
    (biprod.inl : pdCohSub X A U n ⟶ pdCohSub X A U n ⊞ pdCohSub X A V n) cU
      + (biprod.inr : pdCohSub X A V n ⟶ pdCohSub X A U n ⊞ pdCohSub X A V n) cV with hw
  have hG : (honestG X A U V n).hom w = 0 := by
    have h1 : (honestG X A U V n).hom
        ((biprod.inl : pdCohSub X A U n ⟶ pdCohSub X A U n ⊞ pdCohSub X A V n) cU)
        = (pdCohMap X A U (U ∩ V) Set.inter_subset_left n).hom cU := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (honestG_inl' X A U V n)) cU
      rw [ModuleCat.hom_comp] at h
      exact h
    have h2 : (honestG X A U V n).hom
        ((biprod.inr : pdCohSub X A V n ⟶ pdCohSub X A U n ⊞ pdCohSub X A V n) cV)
        = -((pdCohMap X A V (U ∩ V) Set.inter_subset_right n).hom cV) := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (honestG_inr' X A U V n)) cV
      rw [ModuleCat.hom_comp, ModuleCat.hom_neg] at h
      exact h
    rw [hw, map_add, h1, h2, hUV, add_neg_cancel]
  have hex := honest_exact₂ X A U V hU hV hcov n
  have hrange : LinearMap.range (ModuleCat.Hom.hom (honestF X A U V n))
      = LinearMap.ker (ModuleCat.Hom.hom (honestG X A U V n)) :=
    ShortComplex.Exact.moduleCat_range_eq_ker hex
  have hmem : w ∈ LinearMap.range (ModuleCat.Hom.hom (honestF X A U V n)) := by
    rw [hrange]; exact hG
  obtain ⟨τ, hτ⟩ := hmem
  have hfst_inl : ∀ x : pdCohSub X A U n, (ModuleCat.Hom.hom (biprod.fst : pdCohSub X A U n ⊞ pdCohSub X A V n ⟶ pdCohSub X A U n))
      ((ModuleCat.Hom.hom (biprod.inl : pdCohSub X A U n ⟶
        pdCohSub X A U n ⊞ pdCohSub X A V n)) x) = x := by
    intro x
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inl_fst (X := pdCohSub X A U n) (Y := pdCohSub X A V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x
  have hfst_inr : ∀ x : pdCohSub X A V n, (ModuleCat.Hom.hom (biprod.fst : pdCohSub X A U n ⊞ pdCohSub X A V n ⟶ pdCohSub X A U n))
      ((ModuleCat.Hom.hom (biprod.inr : pdCohSub X A V n ⟶
        pdCohSub X A U n ⊞ pdCohSub X A V n)) x) = 0 := by
    intro x
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inr_fst (X := pdCohSub X A U n) (Y := pdCohSub X A V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x
  have hsnd_inl : ∀ x : pdCohSub X A U n, (ModuleCat.Hom.hom (biprod.snd : pdCohSub X A U n ⊞ pdCohSub X A V n ⟶ pdCohSub X A V n))
      ((ModuleCat.Hom.hom (biprod.inl : pdCohSub X A U n ⟶
        pdCohSub X A U n ⊞ pdCohSub X A V n)) x) = 0 := by
    intro x
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inl_snd (X := pdCohSub X A U n) (Y := pdCohSub X A V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x
  have hsnd_inr : ∀ x : pdCohSub X A V n, (ModuleCat.Hom.hom (biprod.snd : pdCohSub X A U n ⊞ pdCohSub X A V n ⟶ pdCohSub X A V n))
      ((ModuleCat.Hom.hom (biprod.inr : pdCohSub X A V n ⟶
        pdCohSub X A U n ⊞ pdCohSub X A V n)) x) = x := by
    intro x
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inr_snd (X := pdCohSub X A U n) (Y := pdCohSub X A V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x
  refine ⟨τ, ?_, ?_⟩
  · have h := congrArg ModuleCat.Hom.hom (honestF_fst' X A U V n)
    rw [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h τ
    rw [LinearMap.comp_apply] at h2
    rw [← h2, hτ, hw, map_add, hfst_inl, hfst_inr, add_zero]
  · have h := congrArg ModuleCat.Hom.hom (honestF_snd' X A U V n)
    rw [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h τ
    rw [LinearMap.comp_apply] at h2
    rw [← h2, hτ, hw, map_add, hsnd_inl, hsnd_inr, zero_add]

end

end Work.Cohomology
