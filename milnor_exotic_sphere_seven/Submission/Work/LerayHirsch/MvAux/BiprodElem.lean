import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Elementwise lemmas for binary biproducts of `ℤ`-modules

This module collects the small elementwise facts about the biproduct `A ⊞ B` of two `ModuleCat ℤ`
objects that the Mayer–Vietoris ladder of `Submission/Work/LerayHirsch/Mv_exact.lean` needs.

The carrier of the categorical biproduct is *not* definitionally the Cartesian product `↑A × ↑B`
(it is the product object built from the limit cone of `ModuleCat`), so the components of an
element have to be read through `biprod.fst` / `biprod.snd`, and elements with prescribed
components have to be built with `biprod.inl` / `biprod.inr`.  The element with components `u` and
`v` is `biprodPair u v = inl u + inr v`; the two projections read the components back
(`biprodPair_fst`, `biprodPair_snd`) and the two together determine the element
(`eq_biprodPair_fst_snd`).
-/

namespace Work.LerayHirsch.MvAux

open CategoryTheory CategoryTheory.Limits

variable {A B C D : ModuleCat ℤ}

/-- The element of the biproduct `A ⊞ B` whose components are `u` and `v`. -/
noncomputable def biprodPair (u : ↑A) (v : ↑B) : ↑(A ⊞ B) :=
  ModuleCat.Hom.hom (biprod.inl : A ⟶ A ⊞ B) u
    + ModuleCat.Hom.hom (biprod.inr : B ⟶ A ⊞ B) v

theorem biprodPair_fst (u : ↑A) (v : ↑B) :
    ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) (biprodPair u v) = u := by
  rw [biprodPair, map_add,
    ← ModuleCat.comp_apply (biprod.inl : A ⟶ A ⊞ B) (biprod.fst : A ⊞ B ⟶ A) u,
    ← ModuleCat.comp_apply (biprod.inr : B ⟶ A ⊞ B) (biprod.fst : A ⊞ B ⟶ A) v,
    biprod.inl_fst, biprod.inr_fst]
  simp

theorem biprodPair_snd (u : ↑A) (v : ↑B) :
    ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) (biprodPair u v) = v := by
  rw [biprodPair, map_add,
    ← ModuleCat.comp_apply (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) u,
    ← ModuleCat.comp_apply (biprod.inr : B ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) v,
    biprod.inl_snd, biprod.inr_snd]
  simp

theorem biprodPair_fst_snd_eq (z : ↑(A ⊞ B)) :
    biprodPair (ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z)
      (ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z) = z := by
  have h0 := congrArg (fun (φ : A ⊞ B ⟶ A ⊞ B) => ModuleCat.Hom.hom φ z)
    (biprod.total (X := A) (Y := B))
  simp only [ModuleCat.hom_add, ModuleCat.hom_id, ModuleCat.comp_apply, LinearMap.add_apply,
    LinearMap.id_apply] at h0
  rw [biprodPair]
  exact h0

theorem eq_biprodPair_fst_snd (z : ↑(A ⊞ B)) :
    z = biprodPair (ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z)
      (ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z) :=
  (biprodPair_fst_snd_eq z).symm

theorem biprodPair_inj {u u' : ↑A} {v v' : ↑B} (h : biprodPair u v = biprodPair u' v') :
    u = u' ∧ v = v' := by
  have h1 := congrArg (fun z => ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z) h
  have h2 := congrArg (fun z => ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z) h
  rw [biprodPair_fst, biprodPair_fst] at h1
  rw [biprodPair_snd, biprodPair_snd] at h2
  exact ⟨h1, h2⟩

theorem biprodPair_eq_zero {u : ↑A} {v : ↑B} : biprodPair u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun z => ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z) h
    have h2 := congrArg (fun z => ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z) h
    rw [biprodPair_fst] at h1
    rw [biprodPair_snd] at h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨rfl, rfl⟩
    rw [biprodPair, map_zero, map_zero, add_zero]

theorem eq_zero_of_biprod_components {z : ↑(A ⊞ B)}
    (h1 : ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z = 0)
    (h2 : ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z = 0) : z = 0 := by
  rw [eq_biprodPair_fst_snd z, h1, h2, biprodPair_eq_zero]
  exact ⟨rfl, rfl⟩

theorem biprod_lift_apply (f : C ⟶ A) (g : C ⟶ B) (x : ↑C) :
    ModuleCat.Hom.hom (biprod.lift f g) x
      = biprodPair (ModuleCat.Hom.hom f x) (ModuleCat.Hom.hom g x) := by
  have h1 : ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A)
      (ModuleCat.Hom.hom (biprod.lift f g) x) = ModuleCat.Hom.hom f x := by
    rw [← ModuleCat.comp_apply (biprod.lift f g) (biprod.fst : A ⊞ B ⟶ A) x, biprod.lift_fst]
  have h2 : ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B)
      (ModuleCat.Hom.hom (biprod.lift f g) x) = ModuleCat.Hom.hom g x := by
    rw [← ModuleCat.comp_apply (biprod.lift f g) (biprod.snd : A ⊞ B ⟶ B) x, biprod.lift_snd]
  rw [← biprodPair_fst_snd_eq (ModuleCat.Hom.hom (biprod.lift f g) x), h1, h2]

theorem biprod_desc_apply (g₁ : A ⟶ C) (g₂ : B ⟶ C) (z : ↑(A ⊞ B)) :
    ModuleCat.Hom.hom (biprod.desc g₁ g₂) z
      = ModuleCat.Hom.hom g₁ (ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z)
        + ModuleCat.Hom.hom g₂ (ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z) := by
  conv_lhs => rw [← biprodPair_fst_snd_eq z]
  rw [biprodPair, map_add,
    ← ModuleCat.comp_apply (biprod.inl : A ⟶ A ⊞ B) (biprod.desc g₁ g₂)
      (ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z),
    ← ModuleCat.comp_apply (biprod.inr : B ⟶ A ⊞ B) (biprod.desc g₁ g₂)
      (ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z),
    biprod.inl_desc, biprod.inr_desc]

theorem biprod_desc_lift_apply (g₁ : A ⟶ C) (g₂ : B ⟶ C) (f₁ : D ⟶ A) (f₂ : D ⟶ B)
    (x : ↑D) :
    ModuleCat.Hom.hom (biprod.desc g₁ g₂) (ModuleCat.Hom.hom (biprod.lift f₁ f₂) x)
      = ModuleCat.Hom.hom g₁ (ModuleCat.Hom.hom f₁ x)
        + ModuleCat.Hom.hom g₂ (ModuleCat.Hom.hom f₂ x) := by
  rw [biprod_desc_apply, biprod_lift_apply, biprodPair_fst, biprodPair_snd]

theorem biprodIsoProd_hom_apply_fst (z : ↑(A ⊞ B)) :
    (ModuleCat.Hom.hom (ModuleCat.biprodIsoProd A B).hom z).1
      = ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z := by
  have h := ModuleCat.biprodIsoProd_inv_comp_fst_apply A B
    (ModuleCat.Hom.hom (ModuleCat.biprodIsoProd A B).hom z)
  rw [ModuleCat.inv_hom_apply] at h
  exact h.symm

theorem biprodIsoProd_hom_apply_snd (z : ↑(A ⊞ B)) :
    (ModuleCat.Hom.hom (ModuleCat.biprodIsoProd A B).hom z).2
      = ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z := by
  have h := ModuleCat.biprodIsoProd_inv_comp_snd_apply A B
    (ModuleCat.Hom.hom (ModuleCat.biprodIsoProd A B).hom z)
  rw [ModuleCat.inv_hom_apply] at h
  exact h.symm

theorem biprodIsoProd_inv_apply_fst (w : ↑A × ↑B) :
    ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A)
        (ModuleCat.Hom.hom (ModuleCat.biprodIsoProd A B).inv w) = w.1 :=
  ModuleCat.biprodIsoProd_inv_comp_fst_apply A B w

theorem biprodIsoProd_inv_apply_snd (w : ↑A × ↑B) :
    ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B)
        (ModuleCat.Hom.hom (ModuleCat.biprodIsoProd A B).inv w) = w.2 :=
  ModuleCat.biprodIsoProd_inv_comp_snd_apply A B w

/-- The pair of components of an element of a biproduct. -/
noncomputable def biprodTofstSnd (z : ↑(A ⊞ B)) : ↑A × ↑B :=
  (ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z,
    ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z)

@[simp] theorem biprodTofstSnd_fst (z : ↑(A ⊞ B)) : (biprodTofstSnd z).1
    = ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A) z := rfl

@[simp] theorem biprodTofstSnd_snd (z : ↑(A ⊞ B)) : (biprodTofstSnd z).2
    = ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B) z := rfl

theorem biprodPair_tofstSnd (z : ↑(A ⊞ B)) :
    biprodPair (biprodTofstSnd z).1 (biprodTofstSnd z).2 = z :=
  biprodPair_fst_snd_eq z

end Work.LerayHirsch.MvAux
