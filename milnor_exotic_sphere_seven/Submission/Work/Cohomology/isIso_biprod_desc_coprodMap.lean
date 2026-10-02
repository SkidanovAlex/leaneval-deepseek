import Mathlib
import Submission.Work.Cohomology.CoprodMVDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `biprod.desc` of two coproduct maps induced by a two-cover is an isomorphism

Let `A`, `B` be index types and `u₁ u₂ : A → B` two maps such that
`Sum.elim u₁ u₂ : A ⊕ A → B` is a bijection -- i.e. `A` double covers `B`.  Then the morphism

`(∐_{a : A} ℤ) ⊞ (∐_{a : A} ℤ) ⟶ ∐_{b : B} ℤ`

of free `ℤ`-modules which sends the first copy of the generator at `a` to the generator at
`u₁ a` and the second copy to the generator at `u₂ a` is an isomorphism.  The reason is that it
factors as the canonical isomorphism `(∐_A ℤ) ⊞ (∐_A ℤ) ≅ ∐_{A ⊕ A} ℤ` followed by
`coprodMap (Sum.elim u₁ u₂)`, and the latter is an isomorphism because `Sum.elim u₁ u₂` is a
bijection.

## Main results

* `coprodMap_id_eq` -- `coprodMap` of an identity map of index types is the identity;
* `isIso_coprodMap_equiv` -- `coprodMap` of an equivalence of index types is an isomorphism;
* `isIso_coprodMap_of_bijective` -- `coprodMap` of a bijection of index types is an isomorphism;
* `isIso_biprod_desc_inl_inr` -- `(∐_A ℤ) ⊞ (∐_A ℤ) ≅ ∐_{A ⊕ A} ℤ`;
* `biprod_desc_coprodMap_factor` -- the factorisation of `biprod.desc` of the two `coprodMap`s
  through `∐_{A ⊕ A} ℤ`;
* `isIso_biprod_desc_coprodMap` -- the target statement.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace Work.Cohomology

noncomputable section

/-! ## `coprodMap` of a bijection of index types -/

/-- `coprodMap` of the identity map of index types is the identity. -/
lemma coprodMap_id_eq {R : Type} [Ring R] {A : Type} :
    coprodMap (R:=R) (id : A → A) = 𝟙 (∐ (fun _ : A => ModuleCat.of R R)) := by
  rw [coprodMap, Sigma.map'_id, Sigma.map_id]

/-- `coprodMap` of an equivalence of index types is an isomorphism; the inverse is
`coprodMap` of the inverse equivalence. -/
lemma isIso_coprodMap_equiv {R : Type} [Ring R] {A S : Type} (e : A ≃ S) :
    IsIso (coprodMap (R:=R) (e : A → S)) := by
  refine IsIso.mk ⟨coprodMap (R:=R) (e.symm : S → A), ?_, ?_⟩
  · rw [coprodMap_comp,
      show ((e.symm : S → A) ∘ (e : A → S)) = id from funext (fun a => e.symm_apply_apply a),
      coprodMap_id_eq]
  · rw [coprodMap_comp,
      show ((e : A → S) ∘ (e.symm : S → A)) = id from funext (fun s => e.apply_symm_apply s),
      coprodMap_id_eq]

/-- `coprodMap` of a bijection of index types is an isomorphism. -/
lemma isIso_coprodMap_of_bijective {R : Type} [Ring R] {A S : Type} (f : A → S)
    (hf : Function.Bijective f) : IsIso (coprodMap (R:=R) f) := by
  have h := isIso_coprodMap_equiv (R:=R) (Equiv.ofBijective f hf)
  simpa [Equiv.coe_ofBijective] using h

/-! ## The canonical isomorphism `(∐_A ℤ) ⊞ (∐_A ℤ) ≅ ∐_{A ⊕ A} ℤ` -/

/-- The morphism `(∐_{a : A} ℤ) ⊞ (∐_{a : A} ℤ) ⟶ ∐_{s : A ⊕ A} ℤ` sending the first copy of
the generator at `a` to the generator at `Sum.inl a` and the second copy to the generator at
`Sum.inr a` is an isomorphism, with inverse given by the coproduct of the two inclusions. -/
lemma isIso_biprod_desc_inl_inr {A : Type} :
    IsIso (biprod.desc (coprodMap (R:=ℤ) (Sum.inl : A → A ⊕ A))
                       (coprodMap (R:=ℤ) (Sum.inr : A → A ⊕ A))) := by
  let eInv : (∐ (fun _ : A ⊕ A => ModuleCat.of ℤ ℤ)) ⟶
      ((∐ (fun _ : A => ModuleCat.of ℤ ℤ)) ⊞ (∐ (fun _ : A => ModuleCat.of ℤ ℤ))) :=
    Sigma.desc (Sum.elim
      (fun a => Sigma.ι (fun _ : A => ModuleCat.of ℤ ℤ) a ≫ biprod.inl)
      (fun a => Sigma.ι (fun _ : A => ModuleCat.of ℤ ℤ) a ≫ biprod.inr))
  refine IsIso.mk ⟨eInv, ?_, ?_⟩
  · -- `(biprod.desc (coprodMap Sum.inl) (coprodMap Sum.inr)) ≫ eInv = 𝟙`
    apply biprod.hom_ext'
    · have h1 : coprodMap (R:=ℤ) (Sum.inl : A → A ⊕ A) ≫ eInv = biprod.inl := by
        apply Sigma.hom_ext
        intro a
        rw [← Category.assoc, ι_coprodMap]
        simp only [eInv]
        rw [Sigma.ι_desc]
        rfl
      rw [← Category.assoc, biprod.inl_desc, h1, Category.comp_id]
    · have h2 : coprodMap (R:=ℤ) (Sum.inr : A → A ⊕ A) ≫ eInv = biprod.inr := by
        apply Sigma.hom_ext
        intro a
        rw [← Category.assoc, ι_coprodMap]
        simp only [eInv]
        rw [Sigma.ι_desc]
        rfl
      rw [← Category.assoc, biprod.inr_desc, h2, Category.comp_id]
  · -- `eInv ≫ (biprod.desc (coprodMap Sum.inl) (coprodMap Sum.inr)) = 𝟙`
    apply Sigma.hom_ext
    intro s
    rw [← Category.assoc]
    cases s with
    | inl a =>
      simp only [eInv, Sigma.ι_desc, Sum.elim_inl]
      rw [Category.assoc, biprod.inl_desc, ι_coprodMap, Category.comp_id]
    | inr a =>
      simp only [eInv, Sigma.ι_desc, Sum.elim_inr]
      rw [Category.assoc, biprod.inr_desc, ι_coprodMap, Category.comp_id]

/-! ## The factorisation of `biprod.desc` of the two `coprodMap`s -/

/-- `biprod.desc (coprodMap u₁) (coprodMap u₂)` factors as the canonical isomorphism
`(∐_A ℤ) ⊞ (∐_A ℤ) ≅ ∐_{A ⊕ A} ℤ` followed by `coprodMap (Sum.elim u₁ u₂)`. -/
lemma biprod_desc_coprodMap_factor {A B : Type} (u₁ u₂ : A → B) :
    biprod.desc (coprodMap (R:=ℤ) u₁) (coprodMap (R:=ℤ) u₂)
      = biprod.desc (coprodMap (R:=ℤ) (Sum.inl : A → A ⊕ A))
                    (coprodMap (R:=ℤ) (Sum.inr : A → A ⊕ A))
        ≫ coprodMap (R:=ℤ) (Sum.elim u₁ u₂) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc]
    rw [biprod.inl_desc, biprod.inl_desc]
    rw [coprodMap_comp]
    congr 1
  · rw [← Category.assoc]
    rw [biprod.inr_desc, biprod.inr_desc]
    rw [coprodMap_comp]
    congr 1

/-! ## The target statement -/

/-- For `u₁ u₂ : A → B` such that `Sum.elim u₁ u₂ : A ⊕ A → B` is a bijection, the map
`(∐_A ℤ) ⊞ (∐_A ℤ) ⟶ ∐_B ℤ` given by `biprod.desc` of the two induced coproduct maps is an
isomorphism. -/
theorem isIso_biprod_desc_coprodMap {A B : Type} (u₁ u₂ : A → B)
    (hw : Function.Bijective (Sum.elim u₁ u₂)) :
    CategoryTheory.IsIso (CategoryTheory.Limits.biprod.desc
      (coprodMap (R:=ℤ) u₁) (coprodMap (R:=ℤ) u₂)) := by
  rw [biprod_desc_coprodMap_factor u₁ u₂]
  haveI := isIso_biprod_desc_inl_inr (A:=A)
  haveI := isIso_coprodMap_of_bijective (R:=ℤ) (Sum.elim u₁ u₂) hw
  infer_instance

end

end Work.Cohomology
