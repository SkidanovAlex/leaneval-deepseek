/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change along a Galois extension, and the Galois action on `X ×_k Spec k'`

For a field extension `k'/k` and a `k`-scheme `X` we set up

* `Work.Descent.Sch k` -- the category `Over (Spec k)` of `k`-schemes;
* `Work.Descent.baseChange k k' X` -- the base change `X ×_k Spec k'`, a `k'`-scheme, and
  `Work.Descent.baseChangeOver k k' X` -- the same scheme viewed as a `k`-scheme;
* `Work.Descent.baseChangeOverπ k k' X : X_{k'} ⟶ X` -- the projection, as a morphism of
  `k`-schemes;
* `Work.Descent.galAct k k' X σ` -- the action of `σ : Gal k k'` on the underlying scheme of
  `X_{k'}`, i.e. the morphism `id_X × Spec σ`; it is a morphism over `X` (`galAct_π`) and hence a
  morphism of `k`-schemes (`galActOver`);
* `Work.Descent.IsGaloisQuotient k k' X` -- the assertion that the projection `X_{k'} ⟶ X` is the
  categorical quotient of `X_{k'}` by this action: every `Γ`-invariant morphism out of `X_{k'}`
  factors uniquely through the projection.

The main theorem of this directory (`Work.Descent.baseChange_isQuotient`) is that
`IsGaloisQuotient k k' X` holds whenever `X` is separated and locally of finite type over `k`; its
corollary `Work.Descent.desc_of_invariant` is the form used for the descent of the group structure.

See `Submission/Work/NOTES_LEAD_jacobian_GC.md` §3.7.
-/
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.Descent

/-- The category of `k`-schemes, i.e. schemes over `Spec k`. -/
abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (.of k))

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The structure morphism `Spec k' ⟶ Spec k` induced by `k → k'`. -/
noncomputable def specMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (.of k') ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- Base change along `Spec k' ⟶ Spec k`, as a functor on schemes over `k`. -/
noncomputable abbrev baseChangeFunctor (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Sch k ⥤ Sch k' :=
  Over.pullback (specMap k k')

/-- The base change `X ×_k Spec k'` of a `k`-scheme `X`, as a `k'`-scheme. -/
noncomputable abbrev baseChange (X : Sch k) : Sch k' := (baseChangeFunctor k k').obj X

@[simp] lemma baseChange_left (X : Sch k) :
    (baseChange (k := k) (k' := k') X).left = pullback X.hom (specMap k k') := rfl

@[simp] lemma baseChange_hom (X : Sch k) :
    (baseChange (k := k) (k' := k') X).hom = pullback.snd X.hom (specMap k k') := rfl

/-- The projection `X_{k'} ⟶ X`, as a morphism of schemes. -/
noncomputable def baseChangeπ (X : Sch k) : (baseChange (k := k) (k' := k') X).left ⟶ X.left :=
  pullback.fst X.hom (specMap k k')

/-- The projection is a morphism over `Spec k`: this is `pullback.condition`. -/
lemma baseChangeπ_hom (X : Sch k) :
    baseChangeπ (k := k) (k' := k') X ≫ X.hom =
      (baseChange (k := k) (k' := k') X).hom ≫ specMap k k' :=
  pullback.condition

/-! ### Basic properties of the projection

The projection `X_{k'} ⟶ X` is the base change of `Spec k' ⟶ Spec k`, which is affine, flat,
surjective and quasi-compact; consequently it is a flat, surjective and quasi-compact morphism,
so Mathlib's effective-epimorphism and descent results for such covers apply to it. -/

instance (X : Sch k) : Flat (baseChangeπ (k := k) (k' := k') X) := by
  rw [baseChangeπ]
  infer_instance

instance (X : Sch k) : Surjective (baseChangeπ (k := k) (k' := k') X) := by
  rw [baseChangeπ]
  infer_instance

instance (X : Sch k) : QuasiCompact (baseChangeπ (k := k) (k' := k') X) := by
  rw [baseChangeπ]
  infer_instance

/-- The projection is an effective epimorphism of schemes. -/
instance (X : Sch k) : EffectiveEpi (baseChangeπ (k := k) (k' := k') X) := inferInstance

/-- The ring homomorphism underlying `Spec.map` for a Galois automorphism. -/
lemma specMap_gal_coe (σ : Gal k k') :
    Spec.map (CommRingCat.ofHom (σ : k' →+* k')) =
      Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := rfl

@[simp] lemma specMap_one :
    Spec.map (CommRingCat.ofHom ((1 : Gal k k') : k' →+* k')) = 𝟙 (Spec (.of k')) := by
  have h : CommRingCat.ofHom ((1 : Gal k k') : k' →+* k') = 𝟙 (CommRingCat.of k') := rfl
  rw [h, Spec.map_id]

lemma specMap_mul (σ τ : Gal k k') :
    Spec.map (CommRingCat.ofHom ((σ * τ : Gal k k') : k' →+* k')) =
      Spec.map (CommRingCat.ofHom (σ : k' →+* k')) ≫
        Spec.map (CommRingCat.ofHom (τ : k' →+* k')) := by
  have h : CommRingCat.ofHom ((σ * τ : Gal k k') : k' →+* k') =
      CommRingCat.ofHom (τ : k' →+* k') ≫ CommRingCat.ofHom (σ : k' →+* k') := by
    ext c
    exact AlgEquiv.mul_apply σ τ c
  rw [h, Spec.map_comp]

/-- The action of `σ : Gal k k'` on the underlying scheme of `X_{k'}`, given by `id_X × Spec σ`. -/
noncomputable def galAct (X : Sch k) (σ : Gal k k') :
    (baseChange (k := k) (k' := k') X).left ⟶ (baseChange (k := k) (k' := k') X).left :=
  pullback.map X.hom (specMap k k') X.hom (specMap k k') (𝟙 X.left)
    (Spec.map (CommRingCat.ofHom (σ : k' →+* k'))) (𝟙 (Spec (.of k)))
    (by simp)
    (by
      rw [Category.comp_id]
      simp only [specMap]
      rw [← Spec.map_comp]
      congr 1
      ext c
      exact (σ.commutes c).symm)

/-- The Galois action is `σ`-semilinear over `Spec k'`: composing with the structure morphism to
`Spec k'` amounts to precomposing with `Spec σ`. -/
lemma galAct_hom (X : Sch k) (σ : Gal k k') :
    galAct (k := k) (k' := k') X σ ≫ (baseChange (k := k) (k' := k') X).hom =
      (baseChange (k := k) (k' := k') X).hom ≫
        Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
  simp [galAct, baseChange_hom, pullback.map, pullback.lift_snd]

/-- The Galois action is over `X`. -/
lemma galAct_π (X : Sch k) (σ : Gal k k') :
    galAct (k := k) (k' := k') X σ ≫ baseChangeπ X = baseChangeπ X := by
  simp [galAct, baseChangeπ, pullback.map, pullback.lift_fst]

@[simp] lemma galAct_one (X : Sch k) :
    galAct (k := k) (k' := k') X 1 = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [galAct, pullback.map, specMap_one]

/-- The Galois action is compatible with the group structure. -/
lemma galAct_mul (X : Sch k) (σ τ : Gal k k') :
    galAct (k := k) (k' := k') X (σ * τ) =
      galAct (k := k) (k' := k') X σ ≫ galAct (k := k) (k' := k') X τ := by
  apply pullback.hom_ext <;>
    simp only [galAct, pullback.map, pullback.lift_fst_assoc, pullback.lift_fst,
      pullback.lift_snd_assoc, pullback.lift_snd, Category.comp_id, Category.id_comp,
      Category.assoc, specMap_mul]

/-- The assertion that `X_{k'} ⟶ X` is the categorical quotient of `X_{k'}` by the action of the
Galois group: every `Γ`-invariant morphism `X_{k'} ⟶ Y` of `k`-schemes factors uniquely through
the projection. -/
def IsGaloisQuotient (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (X : Sch k) : Prop :=
  ∀ (Y : Sch k) (Φ : (baseChange (k := k) (k' := k') X).left ⟶ Y.left),
    Φ ≫ Y.hom = (baseChange (k := k) (k' := k') X).hom ≫ specMap k k' →
    (∀ σ : Gal k k', galAct (k := k) (k' := k') X σ ≫ Φ = Φ) →
      ∃! g : X ⟶ Y, baseChangeπ (k := k) (k' := k') X ≫ g.left = Φ

end Work.Descent
