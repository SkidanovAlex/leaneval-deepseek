/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv, B1: comparison of two base changes of a curve, and `bcDiv`

Setting: fields `K → L → F` and a curve `C` over `K`.  Then `(C_L)_F` and `C_F` are two models
over `F` of the base change of `C` to `F`.  The comparison square `bcSq` of
`Work.BcDiv.BCSquare.cmp` is an isomorphism of `F`-schemes, and the pullback of divisors along
it is the identification

  `Work.BcDiv.bcDiv : Dv (C_L) F ≃+ Dv C F`

of the two divisor groups.  All of area BcDiv is about this identification.

## Main definitions

* `Work.BcDiv.BCSquare.cmp S₁ S₂` — the comparison square `C₁ ⟶ C₂` of two base-change squares
  of the same curve to the same field;
* `Work.BcDiv.BCSquare.cmpIso` — the underlying isomorphism `C₂.left ≅ C₁.left`;
* `Work.BcDiv.bcDiv` — the induced identification of divisor groups.

## Main results

* `Work.BcDiv.BCSquare.ext_π` — a `BCSquare` is determined by its projection;
* `Work.BcDiv.BCSquare.cmp_π_comp`, `…cmp_π_hom`, `…instIsIso_cmp_π`, `…cmp_comp_cmp_π`;
* `Work.BcDiv.BCSquare.divMap_of_π_eq_id` — generalisation of `DivOf.divMap_self`;
* `Work.BcDiv.bcDiv_apply`.
-/
import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_comp
import Submission.Work.SymQuot.DivOf.divMap_self
import Submission.Work.GCBasics.DivApi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.BcDiv

noncomputable section

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]

/-! ### B1.1 A base-change square is determined by its projection -/

/-- A `BCSquare` is determined by its projection (`isPullback` is a proposition). -/
theorem BCSquare.ext_π {C₁ : Curve k} {C₂ : Curve F} {S S' : Curve.BCSquare C₁ C₂}
    (h : S.π = S'.π) : S = S' := by
  obtain ⟨π, hπ⟩ := S
  obtain ⟨π', hπ'⟩ := S'
  simp only at h
  subst h
  rfl

/-! ### B1.2 The comparison of two base changes -/

variable {C : Curve k} {C₁ C₂ : Curve F}

/-- The projection of the comparison square of `S₁` and `S₂`, the canonical map
`C₂.left ⟶ C₁.left` induced by the universal property of the pullback `S₁`. -/
abbrev BCSquare.cmpπ (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    C₂.left ⟶ C₁.left :=
  S₁.isPullback.lift S₂.π C₂.hom S₂.isPullback.w

/-- **The comparison square of two base changes.**  If `S₁ : BCSquare C C₁` and
`S₂ : BCSquare C C₂` are two cartesian squares with the same cospan `C.hom`, `specMap k F`, then
there is a canonical cartesian square `C₁ ⟶ C₂` over `Spec F`: both `C₁` and `C₂` are models of
the same base change. -/
noncomputable def BCSquare.cmp (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    Curve.BCSquare C₁ C₂ where
  π := BCSquare.cmpπ S₁ S₂
  isPullback := by
    have h1 : BCSquare.cmpπ S₁ S₂ ≫ S₁.π = S₂.π := IsPullback.lift_fst _ _ _ _
    have h2 : BCSquare.cmpπ S₁ S₂ ≫ C₁.hom = C₂.hom := IsPullback.lift_snd _ _ _ _
    refine IsPullback.of_right (h₁₁ := BCSquare.cmpπ S₁ S₂) (h₁₂ := S₁.π)
      (h₂₁ := Curve.specMap F F) (h₂₂ := Curve.specMap k F) (v₁₁ := C₂.hom)
      (v₁₂ := C₁.hom) (v₁₃ := C.hom) ?_ ?_ S₁.isPullback
    · rw [h1, Work.SymQuot.DivOf.Work.SymQuot.DivOf.specMap_self F, Category.id_comp]
      exact S₂.isPullback
    · rw [h2, Work.SymQuot.DivOf.Work.SymQuot.DivOf.specMap_self F, Category.comp_id]

theorem BCSquare.cmp_π_comp (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    (BCSquare.cmp S₁ S₂).π ≫ S₁.π = S₂.π :=
  IsPullback.lift_fst _ _ _ _

theorem BCSquare.cmp_π_hom (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    (BCSquare.cmp S₁ S₂).π ≫ C₁.hom = C₂.hom :=
  IsPullback.lift_snd _ _ _ _

/-- Going back and forth between the two models is the identity. -/
theorem BCSquare.cmp_comp_cmp_π (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    ((BCSquare.cmp S₁ S₂).comp (BCSquare.cmp S₂ S₁)).π = 𝟙 C₁.left := by
  refine IsPullback.hom_ext S₁.isPullback ?_ ?_
  · dsimp only [Curve.BCSquare.comp]
    rw [Category.assoc, BCSquare.cmp_π_comp, BCSquare.cmp_π_comp, Category.id_comp]
  · dsimp only [Curve.BCSquare.comp]
    rw [Category.assoc, BCSquare.cmp_π_hom, BCSquare.cmp_π_hom, Category.id_comp]

/-- The comparison of two base changes, as an isomorphism `C₂.left ≅ C₁.left` of underlying
schemes.  It is given by the two comparison projections, which are mutually inverse by
`BCSquare.cmp_comp_cmp_π`. -/
noncomputable def BCSquare.cmpIso (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    C₂.left ≅ C₁.left where
  hom := (BCSquare.cmp S₁ S₂).π
  inv := (BCSquare.cmp S₂ S₁).π
  hom_inv_id := BCSquare.cmp_comp_cmp_π S₂ S₁
  inv_hom_id := BCSquare.cmp_comp_cmp_π S₁ S₂

@[simp]
theorem BCSquare.cmpIso_hom (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    (BCSquare.cmpIso S₁ S₂).hom = (BCSquare.cmp S₁ S₂).π := rfl

@[simp]
theorem BCSquare.cmpIso_inv (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    (BCSquare.cmpIso S₁ S₂).inv = (BCSquare.cmp S₂ S₁).π := rfl

instance BCSquare.instIsIso_cmp_π (S₁ : Curve.BCSquare C C₁) (S₂ : Curve.BCSquare C C₂) :
    IsIso (BCSquare.cmp S₁ S₂).π := by
  rw [← BCSquare.cmpIso_hom S₁ S₂]
  infer_instance

/-- **The pullback of divisors along a square whose projection is the identity does nothing**:
the generalisation of `Work.SymQuot.DivOf.divMap_self` to an arbitrary cartesian square
`C₀ ⟶ C₀` over `Spec F` with projection `𝟙`. -/
theorem BCSquare.divMap_of_π_eq_id {C₀ : Curve F} (S : Curve.BCSquare C₀ C₀)
    (hπ : S.π = 𝟙 C₀.left) : S.divMap = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro D
  apply Finsupp.ext
  intro Q'
  rw [Curve.BCSquare.divMap_apply, Curve.BCSquare.divMapCoeff, AddMonoidHom.id_apply]
  split_ifs with h
  · rw [Work.SymQuot.DivOf.Work.SymQuot.DivOf.under_self S hπ Q' h,
      Work.SymQuot.DivOf.Work.SymQuot.DivOf.ramIdx_self S hπ Q', mul_one]
  · exact absurd (by rw [hπ]; exact Curve.Place.isClosed Q') h

/-! ### B1.3 The identification `bcDiv` of the divisor groups -/

variable {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L] [Algebra K L]
  {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- The tautological base-change square of `C` to `F`. -/
abbrev sqF : Curve.BCSquare C (C.baseChange F) := Curve.bcSquare C F

/-- The base-change square of `C` to `F` through the intermediate field `L`. -/
abbrev sqLF : Curve.BCSquare C ((C.baseChange L).baseChange F) :=
  (Curve.bcSquare C L).comp (Curve.bcSquare (C.baseChange L) F)

/-- **The comparison square `(C_L)_F ⟶ C_F`**: the two models of the base change of `C` to `F`
are canonically isomorphic. -/
abbrev bcSq : Curve.BCSquare ((C.baseChange L).baseChange F) (C.baseChange F) :=
  BCSquare.cmp (sqLF (C := C) (L := L) (F := F)) (sqF (C := C) (F := F))

/-- **The identification of the divisor groups of `(C_L)_F` and `C_F`** over a field `F` which
is an `L`-algebra and (compatibly) a `K`-algebra. -/
def bcDiv : Work.GCBasics.Dv (C.baseChange L) F ≃+ Work.GCBasics.Dv C F where
  toFun := (bcSq (C := C) (L := L) (F := F)).divMap
  invFun := (BCSquare.cmp (sqF (C := C) (F := F)) (sqLF (C := C) (L := L) (F := F))).divMap
  left_inv := fun D => by
    change (BCSquare.cmp sqF sqLF).divMap ((BCSquare.cmp sqLF sqF).divMap D) = D
    rw [← AddMonoidHom.comp_apply,
      ← Curve.BCSquare.divMap_comp (S := BCSquare.cmp sqLF sqF) (T := BCSquare.cmp sqF sqLF),
      BCSquare.divMap_of_π_eq_id _ (BCSquare.cmp_comp_cmp_π sqLF sqF)]
    rfl
  right_inv := fun D => by
    change (BCSquare.cmp sqLF sqF).divMap ((BCSquare.cmp sqF sqLF).divMap D) = D
    rw [← AddMonoidHom.comp_apply,
      ← Curve.BCSquare.divMap_comp (S := BCSquare.cmp sqF sqLF) (T := BCSquare.cmp sqLF sqF),
      BCSquare.divMap_of_π_eq_id _ (BCSquare.cmp_comp_cmp_π sqF sqLF)]
    rfl
  map_add' := map_add _

@[simp]
theorem bcDiv_apply (D : Work.GCBasics.Dv (C.baseChange L) F) :
    bcDiv D = (bcSq (C := C) (L := L) (F := F)).divMap D := rfl

@[simp]
theorem bcDiv_symm_apply (D : Work.GCBasics.Dv C F) :
    (bcDiv (C := C) (L := L) (F := F)).symm D
      = (BCSquare.cmp (sqF (C := C) (F := F)) (sqLF (C := C) (L := L) (F := F))).divMap D :=
  rfl

end

end Work.BcDiv
