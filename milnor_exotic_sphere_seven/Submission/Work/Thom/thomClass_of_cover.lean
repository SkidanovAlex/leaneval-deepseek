import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.Ladder2
import Submission.Work.Thom.transgressionSquare
import Submission.Work.Thom.pdCoh_empty_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open Work.TangentClasses
open Work.Cohomology

namespace Work.Thom

open Bundle CategoryTheory CategoryTheory.Limits

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Index-transport helpers -/

/-- The honest Mayer--Vietoris first map is stable under the `eqToHom` induced by an equality of
degrees. -/
theorem eqToHom_honestF (X : TopCat) (A U V : Set X) {m m' : ℕ} (h : m = m') :
    eqToHom (congrArg (fun k => Work.Cohomology.pdCoh X A k) h)
        ≫ Work.Cohomology.honestF X A U V m'
      = Work.Cohomology.honestF X A U V m
        ≫ eqToHom (congrArg (fun k => Work.Cohomology.pdCohBiprod X A U V k) h) := by
  cases h
  simp [eqToHom_refl]

/-- **Transport of a kernel along an isomorphism.** -/
theorem map_ker_eq_ker {A A' B B' : ModuleCat ℤ} (e : A = A') (e' : B = B')
    (f : A ⟶ B) (f' : A' ⟶ B')
    (h : eqToHom e ≫ f' = f ≫ eqToHom e') :
    Submodule.map (ModuleCat.Hom.hom (eqToHom e)) (LinearMap.ker (ModuleCat.Hom.hom f))
      = LinearMap.ker (ModuleCat.Hom.hom f') := by
  have hh' : ∀ x, ModuleCat.Hom.hom f' (ModuleCat.Hom.hom (eqToHom e) x)
      = ModuleCat.Hom.hom (eqToHom e') (ModuleCat.Hom.hom f x) := by
    intro x
    have hc : ModuleCat.Hom.hom f' ∘ₗ ModuleCat.Hom.hom (eqToHom e)
        = ModuleCat.Hom.hom (eqToHom e') ∘ₗ ModuleCat.Hom.hom f := by
      have := congrArg ModuleCat.Hom.hom h
      rwa [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
    have := LinearMap.congr_fun hc x
    simpa only [LinearMap.comp_apply] using this
  have hLy : ∀ y, ModuleCat.Hom.hom (eqToHom e) (ModuleCat.Hom.hom (inv (eqToHom e)) y) = y := by
    intro y
    have hc : ModuleCat.Hom.hom (eqToHom e) ∘ₗ ModuleCat.Hom.hom (inv (eqToHom e))
        = LinearMap.id := by
      have := congrArg ModuleCat.Hom.hom (IsIso.inv_hom_id (eqToHom e))
      rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at this
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hc y
  have hinj : Function.Injective (ModuleCat.Hom.hom (eqToHom e')) := by
    have hL2 : ModuleCat.Hom.hom (inv (eqToHom e')) ∘ₗ ModuleCat.Hom.hom (eqToHom e')
        = LinearMap.id := by
      have := congrArg ModuleCat.Hom.hom (IsIso.hom_inv_id (eqToHom e'))
      rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at this
    intro a b hab
    have h2 := congrArg (ModuleCat.Hom.hom (inv (eqToHom e'))) hab
    rw [← LinearMap.comp_apply, hL2, LinearMap.id_apply, ← LinearMap.comp_apply, hL2,
      LinearMap.id_apply] at h2
    exact h2
  refine SetLike.ext fun y => ?_
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ModuleCat.Hom.hom f' (ModuleCat.Hom.hom (eqToHom e) x) = 0
    rw [hh' x, show ModuleCat.Hom.hom f x = 0 from hx, map_zero]
  · intro hy
    refine ⟨ModuleCat.Hom.hom (inv (eqToHom e)) y, ?_, hLy y⟩
    change ModuleCat.Hom.hom f (ModuleCat.Hom.hom (inv (eqToHom e)) y) = 0
    apply hinj
    rw [show ModuleCat.Hom.hom (eqToHom e')
        (ModuleCat.Hom.hom f (ModuleCat.Hom.hom (inv (eqToHom e)) y))
        = ModuleCat.Hom.hom f' (ModuleCat.Hom.hom (eqToHom e)
            (ModuleCat.Hom.hom (inv (eqToHom e)) y)) from (hh' _).symm, hLy y,
      show ModuleCat.Hom.hom f' y = 0 from hy, map_zero]

/-- The kernel of a composite with an isomorphism on the *right* is the kernel of the first map. -/
theorem ker_comp_iso {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C) [IsIso g] :
    LinearMap.ker (ModuleCat.Hom.hom (f ≫ g)) = LinearMap.ker (ModuleCat.Hom.hom f) := by
  rw [ModuleCat.hom_comp]
  have hinj : Function.Injective (ModuleCat.Hom.hom g) := by
    have hmono : Mono g := ((isIso_iff_mono_and_epi g).mp inferInstance).1
    exact (ModuleCat.mono_iff_injective g).mp hmono
  refine SetLike.ext fun x => ?_
  change ModuleCat.Hom.hom g (ModuleCat.Hom.hom f x) = 0 ↔ ModuleCat.Hom.hom f x = 0
  constructor
  · intro hx
    exact hinj (by rw [hx, map_zero])
  · intro hx
    rw [hx, map_zero]

/-- **Functoriality of the pair map** (composition), reproved locally to avoid importing the
`dualZ`-clashing module `Submission.Work.Cohomology.cappedPairDefs`. -/
theorem relComplexMap_comp_local {X₁ X₂ X₃ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (A₃ : Set X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hf : ∀ x ∈ A₁, f x ∈ A₂) (hg : ∀ y ∈ A₂, g y ∈ A₃) :
    Work.Cohomology.relComplexMap ℤ A₁ A₃ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = Work.Cohomology.relComplexMap ℤ A₂ A₃ g hg
        ≫ Work.Cohomology.relComplexMap ℤ A₁ A₂ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f ℤ A₁ A₃ (f ≫ g) _ n,
    Work.Cohomology.relComplexMap_f ℤ A₂ A₃ g hg n, Work.Cohomology.relComplexMap_f ℤ A₁ A₂ f hf n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply,
    Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

/-- The pair map does not depend on the proof that the first set is carried into the second. -/
theorem relComplexMap_hcongr_local {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h h' : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂) :
    Work.Cohomology.relComplexMap ℤ A₁ A₂ f h = Work.Cohomology.relComplexMap ℤ A₁ A₂ f h' := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Work.Cohomology.relComplexMap_f]

/-- The pair map depends only on the underlying map. -/
theorem relComplexMap_congr_map_local {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    {f g : X₁ ⟶ X₂} (hfg : f = g)
    (hf : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂)
    (hg : ∀ x ∈ A₁, (ConcreteCategory.hom g) x ∈ A₂) :
    Work.Cohomology.relComplexMap ℤ A₁ A₂ f hf = Work.Cohomology.relComplexMap ℤ A₁ A₂ g hg := by
  subst hfg
  exact relComplexMap_hcongr_local A₁ A₂ f hf hg

/-- **Functoriality of `pdCohRes` in the piece**: restricting a class of the pair `(X,A)` to
`W ⊆ U` is restricting to `U` and then to `W`. -/
theorem pdCohRes_eq_pdCohMap (X : TopCat) (A U W : Set X) (hWU : W ⊆ U) (k : ℕ) :
    Work.Cohomology.pdCohRes X A W k
      = Work.Cohomology.pdCohRes X A U k ≫ Work.Cohomology.pdCohMap X A U W hWU k := by
  simp only [Work.Cohomology.pdCohRes, Work.Cohomology.pdCohMap]
  have e1 : Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥W) (X₂ := X) ℤ
        {y : W | (y : X) ∈ A} A
        (subtypeIncl X W) (fun (y : ↥W) (hy : (y : X) ∈ A) => hy)
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥W) (X₂ := X) ℤ
          {y : W | (y : X) ∈ A} A
          (pdIncl (M := X) U W hWU ≫ subtypeIncl X U)
          (fun (y : ↥W) (hy : (y : X) ∈ A) => hy) :=
    relComplexMap_congr_map_local _ _ (by ext y; rfl) _ _
  have e2 : Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥W) (X₂ := X) ℤ
        {y : W | (y : X) ∈ A} A
        (pdIncl (M := X) U W hWU ≫ subtypeIncl X U)
        (fun (y : ↥W) (hy : (y : X) ∈ A) => hy)
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥U) (X₂ := X) ℤ
          {y : U | (y : X) ∈ A} A
          (subtypeIncl X U) (fun (y : ↥U) (hy : (y : X) ∈ A) => hy)
        ≫ Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥W) (X₂ := TopCat.of ↥U) ℤ
            {y : W | (y : X) ∈ A} {y : U | (y : X) ∈ A}
            (pdIncl (M := X) U W hWU) (fun (y : ↥W) (hy : (y : X) ∈ A) => hy) :=
    relComplexMap_comp_local _ _ _ _ _ (fun (y : ↥W) (hy : (y : X) ∈ A) => hy)
      (fun (y : ↥U) (hy : (y : X) ∈ A) => hy)
  rw [e1, e2, ← HomologicalComplex.homologyMap_comp]

/-- **Naturality of `pdCohRes` with respect to the absolute-relative comparison `pdCohIso`.** -/
theorem pdCohRes_pdCohIso (B : Type) [TopologicalSpace B] (U : Set B) (k : ℕ) :
    Work.Cohomology.pdCohRes (TopCat.of B) (∅ : Set B) U k ≫ (pdCohIso ↥U k).hom
      = (pdCohIso B k).hom ≫ restrCoh U ℤ k := by
  have h := relCohMap_relToAbs (subtypeMap U) {y : U | (y : B) ∈ (∅ : Set B)} (∅ : Set B)
    (fun y hy => hy) ℤ k
  simp only [restrCoh]
  rw [show (pdCohIso ↥U k).hom = relToAbs ℤ {y : U | (y : B) ∈ (∅ : Set B)} k from rfl,
      show (pdCohIso B k).hom = relToAbs ℤ (∅ : Set B) k from rfl]
  rw [show Work.Cohomology.pdCohRes (TopCat.of B) (∅ : Set B) U k
      = relCohMap (subtypeMap U) {y : U | (y : B) ∈ (∅ : Set B)} (∅ : Set B)
          (fun y hy => hy) ℤ k from rfl]
  exact h

/-- **Naturality of `pdCohRes` on a sub-piece, in the comparison `pdCohIso`.** -/
theorem pdCohMap_pdCohIso (B : Type) [TopologicalSpace B] (U W : Set B) (hWU : W ⊆ U) (k : ℕ) :
    Work.Cohomology.pdCohMap (TopCat.of B) (∅ : Set B) U W hWU k ≫ (pdCohIso ↥W k).hom
      = (pdCohIso ↥U k).hom ≫ CohMap (TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU)) ℤ k := by
  have h := relCohMap_relToAbs (TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU))
    {y : W | (y : B) ∈ (∅ : Set B)} {y : U | (y : B) ∈ (∅ : Set B)} (fun y hy => hy) ℤ k
  rw [show (pdCohIso ↥W k).hom = relToAbs ℤ {y : W | (y : B) ∈ (∅ : Set B)} k from rfl,
      show (pdCohIso ↥U k).hom = relToAbs ℤ {y : U | (y : B) ∈ (∅ : Set B)} k from rfl]
  rw [show Work.Cohomology.pdCohMap (TopCat.of B) (∅ : Set B) U W hWU k
      = relCohMap (TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU)) {y : W | (y : B) ∈ (∅ : Set B)}
          {y : U | (y : B) ∈ (∅ : Set B)} (fun y hy => hy) ℤ k from rfl]
  exact h


/-- `PieceRes` to a smaller piece factors through `PieceRes` to a larger one. -/
theorem PieceRes_eq_pdCohMap (Z : RealBundle B F ι) (n : ℕ) {U W : Set B} (hWU : W ⊆ U)
    (τ : OpenThom Z n) :
    PieceRes Z W n τ = (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (fun x hx => hWU hx) n).hom (PieceRes Z U n τ) := by
  have h := pdCohRes_eq_pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
    (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (fun x hx => hWU hx) n
  have h2 := congrArg (fun f => (ModuleCat.Hom.hom f) τ) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- **Restriction-naturality of the local Thom map.**  Restricting the local Thom map over `U` to a
smaller piece `W ⊆ U` is the local Thom map over `W` applied to the restricted base class. -/
theorem localThomMap_restrict (Z : RealBundle B F ι) (n : ℕ) {U W : Set B} (hWU : W ⊆ U)
    (τ : OpenThom Z n) (k : ℕ) :
    CohMap (TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU)) ℤ k
        ≫ ModuleCat.ofHom (localThomMap Z n W (PieceRes Z W n τ) k)
      = ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)
        ≫ pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (fun x hx => hWU hx) (k + n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  simp only [LinearMap.comp_apply]
  rw [localThomMap_apply, localThomMap_apply]
  set AW : Set ↥(Z.proj ⁻¹' W) :=
    (Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z
  set AU : Set ↥(Z.proj ⁻¹' U) :=
    (Subtype.val : ↥(Z.proj ⁻¹' U) → Z.TotalSpace) ⁻¹' zeroComplement Z
  set f : C(↥(Z.proj ⁻¹' W), ↥(Z.proj ⁻¹' U)) :=
    TopCat.Hom.hom (pdIncl (M := TopCat.of Z.TotalSpace)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (fun x hx => hWU hx))
  set inclC : C(↥W, ↥U) := TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU)
  rw [show (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
      (Z.proj ⁻¹' W) (fun x hx => hWU hx) (k + n))
      = relCohMap f AW AU (fun y hy => hy) ℤ (k + n) from rfl]
  have h1 : (CohMap f ℤ k).hom ((CohMap (pieceProj Z U) ℤ k) x)
      = (CohMap (pieceProj Z W) ℤ k).hom ((CohMap inclC ℤ k) x) := by
    have hm : (CohMap (pieceProj Z U) ℤ k ≫ CohMap f ℤ k)
        = (CohMap inclC ℤ k ≫ CohMap (pieceProj Z W) ℤ k) := by
      rw [← CohMap_comp f (pieceProj Z U) ℤ k, ← CohMap_comp (pieceProj Z W) inclC ℤ k]
      congr 1
    have hx := congrArg (fun m => (ModuleCat.Hom.hom m) x) hm
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hx
  have h2 : (relCohMap f AW AU (fun y hy => hy) ℤ n).hom (PieceRes Z U n τ)
      = PieceRes Z W n τ := by
    rw [show (relCohMap f AW AU (fun y hy => hy) ℤ n)
        = pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
            (Z.proj ⁻¹' W) (fun x hx => hWU hx) n from rfl]
    exact (PieceRes_eq_pdCohMap Z n hWU τ).symm
  rw [← h1, ← h2]
  exact (mixedCupC_pairNatural f AW AU (fun y hy => hy) k n
    ((CohMap (pieceProj Z U) ℤ k) x) (PieceRes Z U n τ)).symm


/-- **The morphism form of the naturality of the Thom map under restriction.** -/
theorem thomMap_restrict_mor (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : OpenThom Z n)
    (k : ℕ) :
    restrCoh U ℤ k ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)
      = ModuleCat.ofHom (thomMap Z n τ k) ≫ PieceRes Z U (k + n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, restrCoh]
  exact (thomMap_restrict Z n k U τ x).symm

/-! ## Right-associated forms of the naturality lemmas -/

theorem honestF_fst'_assoc (X : TopCat) (A U V : Set X) (k : ℕ) {Y : ModuleCat ℤ}
    (h : Work.Cohomology.pdCohSub X A U k ⟶ Y) :
    Work.Cohomology.honestF X A U V k ≫ biprod.fst ≫ h
      = Work.Cohomology.pdCohRes X A U k ≫ h := by
  rw [← Category.assoc, Work.Cohomology.honestF_fst']

theorem honestF_snd'_assoc (X : TopCat) (A U V : Set X) (k : ℕ) {Y : ModuleCat ℤ}
    (h : Work.Cohomology.pdCohSub X A V k ⟶ Y) :
    Work.Cohomology.honestF X A U V k ≫ biprod.snd ≫ h
      = Work.Cohomology.pdCohRes X A V k ≫ h := by
  rw [← Category.assoc, Work.Cohomology.honestF_snd']

theorem honestG_inl'_assoc (X : TopCat) (A U V : Set X) (k : ℕ) {Y : ModuleCat ℤ}
    (h : Work.Cohomology.pdCohSub X A (U ∩ V) k ⟶ Y) :
    biprod.inl ≫ Work.Cohomology.honestG X A U V k ≫ h
      = Work.Cohomology.pdCohMap X A U (U ∩ V) Set.inter_subset_left k ≫ h := by
  rw [← Category.assoc, Work.Cohomology.honestG_inl']

theorem honestG_inr'_assoc (X : TopCat) (A U V : Set X) (k : ℕ) {Y : ModuleCat ℤ}
    (h : Work.Cohomology.pdCohSub X A (U ∩ V) k ⟶ Y) :
    biprod.inr ≫ Work.Cohomology.honestG X A U V k ≫ h
      = (-Work.Cohomology.pdCohMap X A V (U ∩ V) Set.inter_subset_right k) ≫ h := by
  rw [← Category.assoc, Work.Cohomology.honestG_inr']

theorem pdCohRes_pdCohIso_assoc (B : Type) [TopologicalSpace B] (U : Set B) (k : ℕ)
    {Y : ModuleCat ℤ} (h : Coh ℤ k ↥U ⟶ Y) :
    Work.Cohomology.pdCohRes (TopCat.of B) (∅ : Set B) U k ≫ (pdCohIso ↥U k).hom ≫ h
      = (pdCohIso B k).hom ≫ (restrCoh U ℤ k ≫ h) := by
  rw [← Category.assoc, pdCohRes_pdCohIso, Category.assoc]

theorem pdCohMap_pdCohIso_assoc (B : Type) [TopologicalSpace B] (U W : Set B) (hWU : W ⊆ U)
    (k : ℕ) {Y : ModuleCat ℤ} (h : Coh ℤ k ↥W ⟶ Y) :
    Work.Cohomology.pdCohMap (TopCat.of B) (∅ : Set B) U W hWU k ≫ (pdCohIso ↥W k).hom ≫ h
      = (pdCohIso ↥U k).hom
        ≫ (CohMap (TopCat.Hom.hom (pdIncl (M := TopCat.of B) U W hWU)) ℤ k ≫ h) := by
  rw [← Category.assoc, pdCohMap_pdCohIso, Category.assoc]

/-- If `K` maps to `⊥` under an isomorphism, then `K = ⊥`. -/
theorem eq_bot_of_map_eq_bot {A A' : ModuleCat ℤ} (e : A = A') (K : Submodule ℤ A)
    (h : Submodule.map (ModuleCat.Hom.hom (eqToHom e)) K = ⊥) : K = ⊥ := by
  have hinv : ModuleCat.Hom.hom (inv (eqToHom e)) ∘ₗ ModuleCat.Hom.hom (eqToHom e)
      = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom (IsIso.hom_inv_id (eqToHom e))
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at this
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h1 : ModuleCat.Hom.hom (eqToHom e) x ∈ (⊥ : Submodule ℤ A') := by
    rw [← h]; exact ⟨x, hx, rfl⟩
  rw [Submodule.mem_bot] at h1
  have h2 := congrArg (ModuleCat.Hom.hom (inv (eqToHom e))) h1
  rw [map_zero] at h2
  rwa [← LinearMap.comp_apply, hinv, LinearMap.id_apply] at h2

/-- **The `F`-square** of the Mayer--Vietoris ladder: the Thom map is compatible with the two
restrictions to the pieces. -/
theorem ladder_F_square (Z : RealBundle B F ι) (n : ℕ) {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (τ : OpenThom Z n) :
    ∀ k : ℕ,
      Work.Cohomology.honestF (TopCat.of B) (∅ : Set B) U V k
          ≫ biprod.map
              ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k))
              ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k))
        = ((pdCohIso B k).hom ≫ ModuleCat.ofHom (thomMap Z n τ k))
          ≫ Work.Cohomology.honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
              (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n) := by
  intro k
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [biprod.map_fst, honestF_fst'_assoc, Work.Cohomology.honestF_fst',
      pdCohRes_pdCohIso_assoc, thomMap_restrict_mor Z n U τ k]
  · simp only [Category.assoc]
    rw [biprod.map_snd, honestF_snd'_assoc, Work.Cohomology.honestF_snd',
      pdCohRes_pdCohIso_assoc, thomMap_restrict_mor Z n V τ k]

/-- **The `G`-square** of the Mayer--Vietoris ladder: the Thom map is compatible with the
difference of the two restrictions to the pieces. -/
theorem ladder_G_square (Z : RealBundle B F ι) (n : ℕ) {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (τ : OpenThom Z n) :
    ∀ k : ℕ,
      Work.Cohomology.honestG (TopCat.of B) (∅ : Set B) U V k
          ≫ ((pdCohIso ↥(U ∩ V) k).hom
              ≫ ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k))
        = biprod.map
              ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k))
              ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k))
          ≫ Work.Cohomology.honestG (TopCat.of Z.TotalSpace) (zeroComplement Z)
              (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n) := by
  intro k
  refine biprod.ext_from_iff.mpr ⟨?_, ?_⟩
  · simp only [Category.assoc]
    rw [honestG_inl'_assoc, biprod.inl_map_assoc, Work.Cohomology.honestG_inl',
      pdCohMap_pdCohIso_assoc, localThomMap_restrict Z n Set.inter_subset_left τ k,
      Category.assoc]
    rfl
  · simp only [Category.assoc]
    rw [honestG_inr'_assoc, biprod.inr_map_assoc, Work.Cohomology.honestG_inr',
      Preadditive.comp_neg, Preadditive.neg_comp, neg_inj, pdCohMap_pdCohIso_assoc,
      localThomMap_restrict Z n Set.inter_subset_right τ k, Category.assoc]
    rfl

/-- **The transgression (δ-)square** of the Mayer--Vietoris ladder: the Thom map is compatible
with the connecting homomorphisms of the base and of the Thom pair. -/
theorem ladder_delta_square (Z : RealBundle B F ι) (n : ℕ) {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (τ : OpenThom Z n) :
    ∀ k : ℕ,
      Work.Cohomology.honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k
          ≫ ((pdCohIso B (k + 1)).hom ≫ ModuleCat.ofHom (thomMap Z n τ (k + 1)))
        = ((pdCohIso ↥(U ∩ V) k).hom
              ≫ ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k))
          ≫ (Work.Cohomology.honestDelta (TopCat.of Z.TotalSpace) (zeroComplement Z)
                (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
                (hV.preimage Z.continuous_proj) (preimage_union_univ Z hcov) (k + n)
              ≫ eqToHom (congrArg (fun m => Work.Cohomology.pdCoh (TopCat.of Z.TotalSpace)
                  (zeroComplement Z) m) (by omega : k + n + 1 = (k + 1) + n))) := by
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  have hts := transgressionSquare B F ι Z n hU hV hcov τ k ((pdCohIso ↥(U ∩ V) k).hom y)
  rw [show (pdCohIso ↥(U ∩ V) k).symm.hom ((pdCohIso ↥(U ∩ V) k).hom y) = y from by
    rw [Iso.symm_hom]; exact Iso.hom_inv_id_apply _ y] at hts
  exact hts


theorem thomClass_of_cover {B : Type} [TopologicalSpace B] (n : ℕ) (hn : 1 ≤ n) (ι : Type)
    [Inhabited ι] (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (τ : Work.Thom.OpenThom Z n)
    (hUloc : Work.Thom.LocalThom Z n U) (hVloc : Work.Thom.LocalThom Z n V)
    (hUVloc : Work.Thom.LocalThom Z n (U ∩ V))
    (hUτ : hUloc.τ = (Work.Thom.PieceRes Z U n) τ)
    (hVτ : hVloc.τ = (Work.Thom.PieceRes Z V n) τ)
    (hUVτ : hUVloc.τ = (Work.Thom.PieceRes Z (U ∩ V) n) τ)
    (hlow : Subsingleton (Work.Thom.PieceCoh Z (U ∩ V) (n - 1))) :
    ∀ k : ℕ, Function.Bijective (Work.Thom.thomMap Z n τ k) := by
  have hcov' : Z.proj ⁻¹' U ∪ Z.proj ⁻¹' V = Set.univ := preimage_union_univ Z hcov
  have hmain := five_lemma_LES'
    (M₁ := fun k => pdCoh (TopCat.of B) (∅ : Set B) k)
    (P₁ := fun k => pdCohBiprod (TopCat.of B) (∅ : Set B) U V k)
    (Q₁ := fun k => pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) k)
    (M₂ := fun k => Work.Thom.OpenThom Z (k + n))
    (P₂ := fun k => pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n))
    (Q₂ := fun k => pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) (k + n))
    (F₁ := fun k => honestF (TopCat.of B) (∅ : Set B) U V k)
    (G₁ := fun k => honestG (TopCat.of B) (∅ : Set B) U V k)
    (δ₁ := fun k => honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k)
    (F₂ := fun k => honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n))
    (G₂ := fun k => honestG (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n))
    (δ₂ := fun k => honestDelta (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
        (hV.preimage Z.continuous_proj) hcov' (k + n)
        ≫ eqToHom (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m)
            (by omega : k + n + 1 = (k + 1) + n)))
    (e₂₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₂ (TopCat.of B) (∅ : Set B) U V hU hV hcov k))
    (e₃₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₃ (TopCat.of B) (∅ : Set B) U V hU hV hcov k))
    (e₁₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₁ (TopCat.of B) (∅ : Set B) U V hU hV hcov k))
    (e₂₂ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₂ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
          (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (k + n)))
    (e₃₂ := fun k => by
      rw [ker_comp_iso]
      exact ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₃ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
          (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (k + n)))
    (e₁₂ := fun k => by
      have hr : LinearMap.range (ModuleCat.Hom.hom (honestDelta (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
            (hV.preimage Z.continuous_proj) hcov' (k + n)))
          = LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
              (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((k + n) + 1))) :=
        ShortComplex.Exact.moduleCat_range_eq_ker
          (honest_exact₁ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
            (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (k + n))
      rw [ModuleCat.hom_comp, LinearMap.range_comp, hr]
      exact map_ker_eq_ker
        (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m)
          (by omega : (k + n) + 1 = (k + 1) + n))
        (congrArg (fun m => pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) m) (by omega : (k + n) + 1 = (k + 1) + n))
        (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((k + n) + 1))
        (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((k + 1) + n))
        (eqToHom_honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V)
          (by omega : (k + n) + 1 = (k + 1) + n)))
    (TM := fun k => (pdCohIso B k).hom ≫ ModuleCat.ofHom (thomMap Z n τ k))
    (TP := fun k => biprod.map
        ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k))
        ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)))
    (TQ := fun k => (pdCohIso ↥(U ∩ V) k).hom
        ≫ ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k))
    (f₁ := by
      haveI : Mono (hmvF (TopCat.of B) (∅ : Set B) U V) :=
        (hmv_shortExact (TopCat.of B) (∅ : Set B) U V).mono_f
      haveI : Mono (HomologicalComplex.homologyMap
          (hmvF (TopCat.of B) (∅ : Set B) U V) 0) := mono_homologyMap_f_zero _
      have heq : honestF (TopCat.of B) (∅ : Set B) U V 0
          = (cmpXIso (TopCat.of B) (∅ : Set B) U V hU hV hcov 0).hom
            ≫ HomologicalComplex.homologyMap (hmvF (TopCat.of B) (∅ : Set B) U V) 0
            ≫ (hmvMidIso (TopCat.of B) (∅ : Set B) U V 0).hom := by
        have hs := honestSq₁ (TopCat.of B) (∅ : Set B) U V 0
        have h := congrArg (fun m => m ≫ (hmvMidIso (TopCat.of B) (∅ : Set B) U V 0).hom) hs
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
        rw [← cmpXIso_hom] at h
        exact h.symm
      have hmono : Mono (honestF (TopCat.of B) (∅ : Set B) U V 0) := by
        rw [heq]
        infer_instance
      rw [LinearMap.ker_eq_bot]
      exact (ModuleCat.mono_iff_injective _).mp hmono)
    (f₂ := by
      have hker_n : LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
          (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)) = ⊥ := by
        have hr : LinearMap.range (ModuleCat.Hom.hom (honestDelta (TopCat.of Z.TotalSpace)
              (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
              (hV.preimage Z.continuous_proj) hcov' (n - 1)))
            = LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
                (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((n - 1) + 1))) :=
          ShortComplex.Exact.moduleCat_range_eq_ker
            (honest_exact₁ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
              (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (n - 1))
        haveI : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) (n - 1)) := hlow
        have hbot : (LinearMap.range (ModuleCat.Hom.hom (honestDelta (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
            (hV.preimage Z.continuous_proj) hcov' (n - 1)))) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro y hy
          obtain ⟨x, rfl⟩ := hy
          rw [show x = 0 from Subsingleton.elim x 0, map_zero]
        have hk : LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((n - 1) + 1))) = ⊥ := by
          rw [← hr, hbot]
        rwa [show (n - 1) + 1 = n from Nat.sub_add_cancel hn] at hk
      have hker0 : LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
          (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n))) = ⊥ := by
        refine eq_bot_of_map_eq_bot
          (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m) (Nat.zero_add n)) _ ?_
        rw [map_ker_eq_ker
          (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m) (Nat.zero_add n))
          (congrArg (fun m => pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) m) (Nat.zero_add n))
          (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n))
          (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
          (eqToHom_honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V)
            (Nat.zero_add n)),
          hker_n]
      intro u hu
      have hu0 : u = 0 := by
        have hz := (Submodule.eq_bot_iff (LinearMap.ker (ModuleCat.Hom.hom (honestF
          (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n))))).mp hker0
        exact hz u (by
          show ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n)) u = 0
          exact hu)
      exact ⟨0, by rw [map_zero, hu0]⟩)
    (hF := ladder_F_square Z n hU hV hcov τ)
    (hG := ladder_G_square Z n hU hV hcov τ)
    (hδ := ladder_delta_square Z n hU hV hcov τ)
    (hP := by
      intro k
      have hbU : Function.Bijective (localThomMap Z n U (PieceRes Z U n τ) k) := by
        rw [← hUτ]; exact hUloc.isThom k
      have hbV : Function.Bijective (localThomMap Z n V (PieceRes Z V n τ) k) := by
        rw [← hVτ]; exact hVloc.isThom k
      haveI : IsIso (ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr hbU.1,
          (ModuleCat.epi_iff_surjective _).mpr hbU.2⟩
      haveI : IsIso (ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr hbV.1,
          (ModuleCat.epi_iff_surjective _).mpr hbV.2⟩
      haveI hiU : IsIso ((pdCohIso ↥U k).hom
          ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)) :=
        ((pdCohIso ↥U k).trans
          (asIso (ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)))).isIso_hom
      haveI hiV : IsIso ((pdCohIso ↥V k).hom
          ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)) :=
        ((pdCohIso ↥V k).trans
          (asIso (ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)))).isIso_hom
      exact (biprod.mapIso
        (asIso ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)))
        (asIso ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)))).isIso_hom)
    (hQ := by
      intro k
      have hbUV : Function.Bijective (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k) := by
        rw [← hUVτ]; exact hUVloc.isThom k
      haveI : IsIso (ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr hbUV.1,
          (ModuleCat.epi_iff_surjective _).mpr hbUV.2⟩
      haveI : IsIso ((pdCohIso ↥(U ∩ V) k).hom
          ≫ ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k)) :=
        ((pdCohIso ↥(U ∩ V) k).trans
          (asIso (ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k)))).isIso_hom
      exact ‹_›)
  intro k
  haveI hk := hmain k
  haveI hthom : IsIso (ModuleCat.ofHom (thomMap Z n τ k)) :=
    IsIso.of_isIso_comp_left (pdCohIso B k).hom (ModuleCat.ofHom (thomMap Z n τ k))
  rw [isIso_iff_mono_and_epi] at hthom
  exact ⟨(ModuleCat.mono_iff_injective _).mp hthom.1,
    (ModuleCat.epi_iff_surjective _).mp hthom.2⟩

end

end Work.Thom
