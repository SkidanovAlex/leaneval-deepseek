import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.Coprod.quasiIso_colimMap
import Submission.Work.TOOLKIT.Coprod.hq_sigma_bijective

open CategoryTheory Limits
open _root_.LightCondensed

noncomputable section

set_option linter.style.haveILetI false

namespace Work.TOOLKIT.Sigma

variable {J : Type}

/-- The quotient functor `Cpx ⤤ KCat` (the localization at homotopy equivalences). -/
private abbrev qF : Cpx ⥤ KCat := HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)

/-- The class of quasi-isomorphisms in the homotopy category. -/
private abbrev wq : MorphismProperty KCat :=
  HomotopyCategory.quasiIso LightCondAb (ComplexShape.up ℤ)

/-- The inverse of an isomorphism, packaged so that its source and target are explicit. -/
private noncomputable def invOfIso {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    Y ⟶ X := CategoryTheory.inv f

@[simp] private lemma invOfIso_comp {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    invOfIso f ≫ f = 𝟙 Y := IsIso.inv_hom_id f

@[simp] private lemma comp_invOfIso {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    f ≫ invOfIso f = 𝟙 X := IsIso.hom_inv_id f

@[simp] private lemma invOfIso_comp_assoc {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    [IsIso f] (h : Y ⟶ Z) : invOfIso f ≫ f ≫ h = h := IsIso.inv_hom_id_assoc f h

@[simp] private lemma comp_invOfIso_assoc {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    [IsIso f] (h : X ⟶ Z) : f ≫ invOfIso f ≫ h = h := by
  rw [← Category.assoc, comp_invOfIso, Category.id_comp]

private lemma Qh_map_zero (K L : Cpx) :
    DerivedCategory.Qh.map (0 : qF.obj K ⟶ qF.obj L) = 0 := by simp

/-- **Coproducts of quasi-isomorphisms are quasi-isomorphisms.**  This is the instance
`J = Discrete J'` of `Work.TOOLKIT.Coprod.quasiIso_colimMap`: `LightCondAb` satisfies AB4,
hence the colimit functor is exact and preserves quasi-isomorphisms. -/
private theorem quasiIso_sigma_map (J : Type) (K L : J → Cpx) [HasCoproduct K] [HasCoproduct L]
    (f : ∀ j, K j ⟶ L j) (hf : ∀ j, QuasiIso (f j)) : QuasiIso (Limits.Sigma.map f) := by
  let τ : Discrete.functor K ⟶ Discrete.functor L := Discrete.natTrans (fun j => f j.as)
  have h := Work.TOOLKIT.Coprod.quasiIso_colimMap (J := Discrete J)
    (F := Discrete.functor K) (G := Discrete.functor L) τ (fun j => hf j.as)
  have heq : colimMap τ = Limits.Sigma.map f := by
    apply Limits.Sigma.hom_ext
    intro j
    calc Limits.Sigma.ι K j ≫ colimMap τ
        = τ.app (Discrete.mk j) ≫ Limits.Sigma.ι L j := ι_colimMap _ _
      _ = f j ≫ Limits.Sigma.ι L j := rfl
      _ = Limits.Sigma.ι K j ≫ Limits.Sigma.map f := (Limits.Sigma.ι_map f j).symm
  rwa [heq] at h

/-- Conjugation of the "components" map by an isomorphism of the target preserves bijectivity. -/
private lemma bijective_postcomp_iso {C : Type*} [Category C] {I : Type} {S : I → C} {X Z Z' : C}
    (c : ∀ i, S i ⟶ X) (e : Z ≅ Z') :
    Function.Bijective (fun f : X ⟶ Z => fun i => c i ≫ f) ↔
      Function.Bijective (fun f : X ⟶ Z' => fun i => c i ≫ f) := by
  constructor
  · intro h
    constructor
    · intro f₁ f₂ hf
      have h2 : (fun i => c i ≫ f₁ ≫ e.inv) = (fun i => c i ≫ f₂ ≫ e.inv) := by
        funext i
        have hfi : c i ≫ f₁ = c i ≫ f₂ := congrFun hf i
        simpa [Category.assoc] using congrArg (fun t : S i ⟶ Z' => t ≫ e.inv) hfi
      have h3 : f₁ ≫ e.inv = f₂ ≫ e.inv := h.1 h2
      have h4 := congrArg (fun t : X ⟶ Z => t ≫ e.hom) h3
      simpa [Category.assoc] using h4
    · intro v
      obtain ⟨f, hf⟩ := h.2 (fun i => v i ≫ e.inv)
      refine ⟨f ≫ e.hom, ?_⟩
      funext i
      have hfi : c i ≫ f = v i ≫ e.inv := congrFun hf i
      show c i ≫ (f ≫ e.hom) = v i
      rw [← Category.assoc, hfi]
      simp
  · intro h
    constructor
    · intro f₁ f₂ hf
      have h2 : (fun i => c i ≫ f₁ ≫ e.hom) = (fun i => c i ≫ f₂ ≫ e.hom) := by
        funext i
        have hfi : c i ≫ f₁ = c i ≫ f₂ := congrFun hf i
        simpa [Category.assoc] using congrArg (fun t : S i ⟶ Z => t ≫ e.hom) hfi
      have h3 : f₁ ≫ e.hom = f₂ ≫ e.hom := h.1 h2
      have h4 := congrArg (fun t : X ⟶ Z' => t ≫ e.inv) h3
      simpa [Category.assoc] using h4
    · intro v
      obtain ⟨f, hf⟩ := h.2 (fun i => v i ≫ e.hom)
      refine ⟨f ≫ e.inv, ?_⟩
      funext i
      have hfi : c i ≫ f = v i ≫ e.hom := congrFun hf i
      show c i ≫ (f ≫ e.inv) = v i
      rw [← Category.assoc, hfi]
      simp

/-- If a chain map is zero in `D(LightCondAb)`, then it can be killed up to homotopy by a
quasi-isomorphism (with a complex as source). -/
private lemma exists_quasiIso_homotopy_of_Q_map_eq_zero {K L : Cpx} (k : K ⟶ L)
    (hk : DerivedCategory.Q.map k = 0) :
    ∃ (K' : Cpx) (t : K' ⟶ K), QuasiIso t ∧ Nonempty (Homotopy (t ≫ k) 0) := by
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality (C := LightCondAb) k
  have hq : DerivedCategory.Qh.map (qF.map k) = 0 := by
    have h1 : DerivedCategory.Qh.map (qF.map k) ≫
        (DerivedCategory.quotientCompQhIso LightCondAb).hom.app L = 0 := by
      rw [hnat, hk, comp_zero]
    calc DerivedCategory.Qh.map (qF.map k)
        = (DerivedCategory.Qh.map (qF.map k) ≫
            (DerivedCategory.quotientCompQhIso LightCondAb).hom.app L) ≫
              (DerivedCategory.quotientCompQhIso LightCondAb).inv.app L := by
          rw [Category.assoc]; simp
      _ = 0 := by rw [h1, zero_comp]
  obtain ⟨Z, t, ht, hcomp⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh wq (qF.map k) 0).1
      (by rw [hq, Qh_map_zero])
  obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨t', ht'⟩ := (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map_surjective t
  have htq : QuasiIso t' :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff t').1 (by rw [ht']; exact ht)
  have h1 : qF.map (t' ≫ k) = 0 := by
    rw [Functor.map_comp, ht']
    simpa using hcomp
  refine ⟨K', t', htq, ?_⟩
  exact (HomotopyCategory.quotient_map_eq_zero_iff (t' ≫ k)).1 h1

/-- The components map is bijective for targets in the image of the localization functor. -/
private theorem bijective_image (K : J → Cpx) [HasCoproduct K] (Kot : Cpx) :
    Function.Bijective (fun g : DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj Kot =>
      fun j => DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ g) := by
  constructor
  · intro F F' hFF'
    have key : ∀ F : DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj Kot,
        (∀ j, DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ F = 0) → F = 0 := by
      intro F hF
      obtain ⟨Y', g, s, hs, hfac⟩ := DerivedCategory.left_fac F
      haveI : IsIso (DerivedCategory.Q.map s) := hs
      have hcancel : F ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map g := by
        rw [hfac, Category.assoc]; simp
      have hk : ∀ j, DerivedCategory.Q.map (Limits.Sigma.ι K j ≫ g) = 0 := fun j => by
        have h4 : DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ F ≫ DerivedCategory.Q.map s = 0 := by
          simpa using congrArg (fun t => t ≫ DerivedCategory.Q.map s) (hF j)
        rw [hcancel] at h4
        simpa [Functor.map_comp] using h4
      choose K'' t ht hhom using fun j =>
        exists_quasiIso_homotopy_of_Q_map_eq_zero (Limits.Sigma.ι K j ≫ g) (hk j)
      letI : HasCoproduct K'' := inferInstance
      let T : (∐K'') ⟶ (∐K) := Limits.Sigma.map t
      have hT : QuasiIso T := quasiIso_sigma_map J K'' K t ht
      have hcomp : ∀ j, Homotopy (Limits.Sigma.ι K'' j ≫ T ≫ g) 0 := fun j => by
        have h1 : Limits.Sigma.ι K'' j ≫ T = t j ≫ Limits.Sigma.ι K j := Limits.Sigma.ι_map t j
        have h2 : Homotopy (t j ≫ (Limits.Sigma.ι K j ≫ g)) 0 := (hhom j).some
        rw [← Category.assoc, h1]
        simpa only [Category.assoc] using h2
      -- `T ≫ g` is null-homotopic because all of its components along the coproduct are
      have hTg : Homotopy (T ≫ g) 0 :=
        Work.TOOLKIT.Coprod.homotopy_sigma_desc (K := K'') (f := T ≫ g) (g := 0)
          (fun j => by simpa using hcomp j)
      have hzero : DerivedCategory.Q.map (T ≫ g) = 0 := by
        have h1 : DerivedCategory.Q.map (T ≫ g) = DerivedCategory.Q.map (0 : (∐K'') ⟶ Y') :=
          HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy hTg
        rw [h1]; simp
      haveI : IsIso (DerivedCategory.Q.map T) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) T).2 hT
      let Ti : DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj (∐K'') :=
        invOfIso (DerivedCategory.Q.map T)
      have hg0 : DerivedCategory.Q.map g = 0 := by
        have h1 : DerivedCategory.Q.map T ≫ DerivedCategory.Q.map g = 0 := by
          rw [← Functor.map_comp, hzero]
        have h2 : DerivedCategory.Q.map g = Ti ≫
            (DerivedCategory.Q.map T ≫ DerivedCategory.Q.map g) := by
          rw [← Category.assoc, invOfIso_comp, Category.id_comp]
        rw [h2, h1]; simp
      rw [hfac, hg0]; simp
    have hsub : ∀ j, DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ (F - F') = 0 := fun j => by
      rw [Preadditive.comp_sub, sub_eq_zero]
      exact congrFun hFF' j
    exact sub_eq_zero.mp (key (F - F') hsub)
  · intro v
    choose K' s hs b hfac using fun j => DerivedCategory.right_fac (v j)
    letI : HasCoproduct K' := inferInstance
    have hsQ : ∀ j, QuasiIso (s j) := fun j =>
      (DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) (s j)).1 (hs j)
    have hS : QuasiIso (Limits.Sigma.map s) := quasiIso_sigma_map J K' K s hsQ
    let S : DerivedCategory.Q.obj (∐K') ⟶ DerivedCategory.Q.obj (∐K) :=
      DerivedCategory.Q.map (Limits.Sigma.map s)
    haveI : IsIso S := (DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb)
      (Limits.Sigma.map s)).2 hS
    refine ⟨invOfIso S ≫ DerivedCategory.Q.map (Limits.Sigma.desc b), ?_⟩
    funext j
    let σ : DerivedCategory.Q.obj (K' j) ⟶ DerivedCategory.Q.obj (K j) :=
      DerivedCategory.Q.map (s j)
    let ι : DerivedCategory.Q.obj (K j) ⟶ DerivedCategory.Q.obj (∐K) :=
      DerivedCategory.Q.map (Limits.Sigma.ι K j)
    let ι' : DerivedCategory.Q.obj (K' j) ⟶ DerivedCategory.Q.obj (∐K') :=
      DerivedCategory.Q.map (Limits.Sigma.ι K' j)
    let C : DerivedCategory.Q.obj (∐K') ⟶ DerivedCategory.Q.obj Kot :=
      DerivedCategory.Q.map (Limits.Sigma.desc b)
    haveI : IsIso σ := hs j
    have h2 : ι' ≫ S = σ ≫ ι := by
      simp only [ι, ι', σ, S, ← Functor.map_comp, Limits.Sigma.ι_map s j]
    have hbj : ι' ≫ C = DerivedCategory.Q.map (b j) := by
      simp only [ι', C, ← Functor.map_comp, Limits.Sigma.ι_comp_desc]
    have h3 : ι ≫ invOfIso S = invOfIso σ ≫ ι' := by
      calc ι ≫ invOfIso S = invOfIso σ ≫ (σ ≫ ι) ≫ invOfIso S := by simp [Category.assoc]
        _ = invOfIso σ ≫ (ι' ≫ S) ≫ invOfIso S := by rw [h2]
        _ = invOfIso σ ≫ ι' := by simp [Category.assoc]
    show ι ≫ (invOfIso S ≫ C) = v j
    calc ι ≫ (invOfIso S ≫ C) = (ι ≫ invOfIso S) ≫ C := by simp [Category.assoc]
      _ = (invOfIso σ ≫ ι') ≫ C := by rw [h3]
      _ = invOfIso σ ≫ (ι' ≫ C) := by simp [Category.assoc]
      _ = invOfIso σ ≫ DerivedCategory.Q.map (b j) := by rw [hbj]
      _ = v j := (hfac j).symm

/-- The localization functor `Q : Cpx ⤤ D(LightCondAb)` preserves small coproducts: for every
family of complexes `K` and every `W` in the derived category, every family of morphisms
`Q(K j) ⟶ W` extends uniquely to a morphism `Q(∐ K) ⟶ W` out of the localization of the
coproduct.  Equivalently, the canonical comparison map `∐ j, Q(K j) ⟶ Q(∐ K)` is an
isomorphism (tested on `Hom(-, W)` by Yoneda, using that `Q` is essentially surjective).
Route: quasi-isomorphisms are stable under coproducts, so the category of acyclic complexes is
a localizing subcategory of `K(LightCondAb)` closed under coproducts; the quotient functor of a
Verdier quotient by a coproduct-closed localizing subcategory preserves coproducts. -/
theorem hom_coproduct_bijective (J : Type) (K : J → Work.TOOLKIT.Cpx)
    [CategoryTheory.Limits.HasCoproduct K] (W : Work.TOOLKIT.DCat) :
    Function.Bijective (fun g : DerivedCategory.Q.obj (CategoryTheory.Limits.sigmaObj K) ⟶ W =>
      fun j => CategoryTheory.CategoryStruct.comp
        (DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι K j)) g) := by
  haveI hEss : DerivedCategory.Q.EssSurj :=
    Localization.essSurj DerivedCategory.Q
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))
  have h := bijective_image K (DerivedCategory.Q.objPreimage W)
  have hconj := bijective_postcomp_iso (C := Work.TOOLKIT.DCat)
    (S := fun j => DerivedCategory.Q.obj (K j))
    (X := DerivedCategory.Q.obj (CategoryTheory.Limits.sigmaObj K))
    (c := fun j => DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι K j))
    (DerivedCategory.Q.objObjPreimageIso W)
  exact hconj.1 h

end Work.TOOLKIT.Sigma
