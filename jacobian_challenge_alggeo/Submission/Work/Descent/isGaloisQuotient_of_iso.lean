/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `IsGaloisQuotient` is invariant under isomorphism of the base scheme

If `e : X ≅ Y` is an isomorphism of `k`-schemes then `X` is a Galois quotient of `X_{k'}` by the
action of `Gal k k'` if and only if `Y` is.  This is a purely formal consequence of the naturality
of base change along `Spec k' ⟶ Spec k`:

* `baseChange_map_fst` -- the projection `baseChangeπ` is natural;
* `galAct_naturality` -- the Galois action is natural;
* `baseChange_map_(inv_)hom` -- base change carries an isomorphism to an isomorphism.

The main lemma `IsGaloisQuotient.of_iso` transports a factorisation along `e`, and the target
`isGaloisQuotient_of_iso` applies it in both directions (using `e.symm`).
-/
import Mathlib
import Submission.Work.Descent.Scheme

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

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- **Naturality of the projection.**  For a morphism `f : X ⟶ Y` of `k`-schemes, the induced
morphism `X_{k'} ⟶ Y_{k'}` on base changes is compatible with the projections `X_{k'} ⟶ X` and
`Y_{k'} ⟶ Y`. -/
lemma baseChange_map_fst {X Y : Sch k} (f : X ⟶ Y) :
    ((baseChangeFunctor k k').map f).left ≫ baseChangeπ Y = baseChangeπ X ≫ f.left := by
  simp only [baseChangeFunctor, Over.pullback_map_left, baseChangeπ, pullback.lift_fst]

/-- The second projection of the morphism `galAct X σ`, i.e. the "action on the `k'`-factor". -/
lemma galAct_snd (X : Sch k) (σ : Gal k k') :
    galAct X σ ≫ (baseChange (k := k) (k' := k') X).hom =
      (baseChange (k := k) (k' := k') X).hom ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
  simp only [galAct, pullback.map, baseChange_hom, pullback.lift_snd]

/-- The Galois action is over `X` (unfolded form of `galAct_π`). -/
lemma galAct_fst (X : Sch k) (σ : Gal k k') :
    galAct X σ ≫ pullback.fst X.hom (specMap k k') = pullback.fst X.hom (specMap k k') :=
  galAct_π X σ

/-- `galAct_snd` in unfolded (`pullback`) form. -/
lemma galAct_snd' (X : Sch k) (σ : Gal k k') :
    galAct X σ ≫ pullback.snd X.hom (specMap k k') =
      pullback.snd X.hom (specMap k k') ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) :=
  galAct_snd X σ

/-- The induced morphism on base changes is compatible with the second projection as well. -/
lemma baseChange_map_snd' {X Y : Sch k} (f : X ⟶ Y) :
    ((baseChangeFunctor k k').map f).left ≫ pullback.snd Y.hom (specMap k k') =
      pullback.snd X.hom (specMap k k') := by
  rw [← baseChange_hom (k := k) (k' := k') Y, Over.w ((baseChangeFunctor k k').map f),
    baseChange_hom (k := k) (k' := k') X]

/-- `baseChange_map_fst` in unfolded (`pullback`) form. -/
lemma baseChange_map_fst' {X Y : Sch k} (f : X ⟶ Y) :
    ((baseChangeFunctor k k').map f).left ≫ pullback.fst Y.hom (specMap k k') =
      pullback.fst X.hom (specMap k k') ≫ f.left :=
  baseChange_map_fst f

/-- **Naturality of the Galois action.**  Base change along `Spec k' ⟶ Spec k` commutes with the
action of `Gal k k'`. -/
lemma galAct_naturality {X Y : Sch k} (f : X ⟶ Y) (σ : Gal k k') :
    galAct X σ ≫ ((baseChangeFunctor k k').map f).left =
      ((baseChangeFunctor k k').map f).left ≫ galAct Y σ := by
  apply pullback.hom_ext (f := Over.hom Y) (g := specMap k k')
  · have hL : (galAct X σ ≫ ((baseChangeFunctor k k').map f).left) ≫
        pullback.fst Y.hom (specMap k k') = pullback.fst X.hom (specMap k k') ≫ f.left := by
      rw [Category.assoc, baseChange_map_fst', ← Category.assoc, galAct_fst]
    have hR : (((baseChangeFunctor k k').map f).left ≫ galAct Y σ) ≫
        pullback.fst Y.hom (specMap k k') = pullback.fst X.hom (specMap k k') ≫ f.left := by
      rw [Category.assoc, galAct_fst, baseChange_map_fst']
    rw [hL, hR]
  · have hL : (galAct X σ ≫ ((baseChangeFunctor k k').map f).left) ≫
        pullback.snd Y.hom (specMap k k') =
        pullback.snd X.hom (specMap k k') ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
      rw [Category.assoc, baseChange_map_snd', galAct_snd']
    have hR : (((baseChangeFunctor k k').map f).left ≫ galAct Y σ) ≫
        pullback.snd Y.hom (specMap k k') =
        pullback.snd X.hom (specMap k k') ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
      rw [Category.assoc, galAct_snd', ← Category.assoc, baseChange_map_snd']
    rw [hL, hR]

/-- Base change carries an isomorphism to an isomorphism (one composite). -/
lemma baseChange_map_inv_hom {X Y : Sch k} (e : X ≅ Y) :
    ((baseChangeFunctor k k').map e.inv).left ≫ ((baseChangeFunctor k k').map e.hom).left =
      𝟙 (baseChange (k := k) (k' := k') Y).left := by
  rw [← Over.comp_left, ← Functor.map_comp, e.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Over.id_left]

/-- Base change carries an isomorphism to an isomorphism (the other composite). -/
lemma baseChange_map_hom_inv {X Y : Sch k} (e : X ≅ Y) :
    ((baseChangeFunctor k k').map e.hom).left ≫ ((baseChangeFunctor k k').map e.inv).left =
      𝟙 (baseChange (k := k) (k' := k') X).left := by
  rw [← Over.comp_left, ← Functor.map_comp, e.hom_inv_id]
  rw [CategoryTheory.Functor.map_id, Over.id_left]

/-- **Transport of the Galois quotient property along an isomorphism.**  If `X_{k'} ⟶ X` is the
categorical quotient of `X_{k'}` by `Gal k k'` and `X ≅ Y`, then the same holds for `Y`. -/
lemma IsGaloisQuotient.of_iso {X Y : Sch k} (e : X ≅ Y) :
    IsGaloisQuotient k k' X → IsGaloisQuotient k k' Y := by
  intro hX Z Φ hΦ hInv
  have hΦ' : (((baseChangeFunctor k k').map e.hom).left ≫ Φ) ≫ Z.hom =
      (baseChange (k := k) (k' := k') X).hom ≫ specMap k k' := by
    rw [Category.assoc, hΦ, ← Category.assoc,
      Over.w ((baseChangeFunctor k k').map e.hom)]
  have hInv' : ∀ σ : Gal k k',
      galAct X σ ≫ ((baseChangeFunctor k k').map e.hom).left ≫ Φ =
        ((baseChangeFunctor k k').map e.hom).left ≫ Φ := by
    intro σ
    rw [← Category.assoc, galAct_naturality e.hom σ, Category.assoc, hInv σ]
  obtain ⟨g₀, hg₀, huniq⟩ := hX Z (((baseChangeFunctor k k').map e.hom).left ≫ Φ) hΦ' hInv'
  refine ⟨e.inv ≫ g₀, ?_, ?_⟩
  · show baseChangeπ Y ≫ Over.Hom.left (e.inv ≫ g₀) = Φ
    rw [Over.comp_left, ← Category.assoc, ← baseChange_map_fst e.inv, Category.assoc, hg₀,
      ← Category.assoc, baseChange_map_inv_hom, Category.id_comp]
  · intro g hg
    have h : e.hom ≫ g = g₀ := by
      refine huniq (e.hom ≫ g) ?_
      show baseChangeπ X ≫ Over.Hom.left (e.hom ≫ g) = _
      rw [Over.comp_left, ← Category.assoc, ← baseChange_map_fst e.hom, Category.assoc, hg]
    rw [← Category.id_comp g, ← e.inv_hom_id, Category.assoc, h]

theorem isGaloisQuotient_of_iso {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X Y : Work.Descent.Sch k} (e : X ≅ Y) :
    (Work.Descent.IsGaloisQuotient k k' X ↔ Work.Descent.IsGaloisQuotient k k' Y) :=
  ⟨IsGaloisQuotient.of_iso e, IsGaloisQuotient.of_iso e.symm⟩

end Work.Descent
