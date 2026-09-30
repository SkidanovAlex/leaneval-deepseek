/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): the definitions

This file sets up the vocabulary of the RESID layer of area **DM** of the Jacobian drive
(`NOTES_LEAD_jacobian_GC.md` §3.3): for a curve `C/K`, symmetric powers
`symGeom : ∀ n, SpecLin.SymGeom C n`, a `K`-scheme `X` and morphisms
`a : X ⟶ Sym^r C`, `b : X ⟶ Sym^{r+m} C`, the *residue map* is the rational map
`σ : X ⤏ Sym^m C` whose value at a point `p` of `X` is the effective representative of the
class of the divisor `divOf (b p) - divOf (a p)`.

The main definitions are

* `Work.Domain.Resid.divD symGeom a b p = divOf (b p) - divOf (a p)`, a divisor of `C_F` for
  an `F`-point `p` of `X`, of degree `m`;
* `Work.Domain.Resid.Rel symGeom a b p y`: `divOf y + divOf (a p) ~ divOf (b p)`, i.e. `y` is
  a point of `Sym^m C` representing the class of `divOf (b p) - divOf (a p)`;
* `Work.Domain.Resid.addMor`: the "addition" of a point of `Sym^r C` and a point of `Sym^m C`,
  as a morphism of `K`-schemes (this is the only piece of area `SY` beyond
  `SpecLin.SymGeom` that RESID needs);
* `Work.Domain.Resid.valueOf`: the value of a rational map at a point of its domain, as an
  `F`-point (this is `Work.GroupChunk.value`, restated here so that area `DM` does not depend
  on area `GC`);
* `Work.Domain.Resid.ResidMap`: the RESID specification (VALUE and DEFINED).

Everything is stated in terms of the interfaces `Work.SpecLin.DivBase C` (area `CB`) and
`Work.SpecLin.SymGeom C n` (area `SY`), exactly as declared in
`Submission/Work/SpecLin/Interface.lean`, and of the shared conventions `Work.GCBasics`
(area `GB`).
-/
import Submission.Work.GCBasics.Basic
import Submission.Work.GCBasics.Points
import Submission.Work.GCBasics.DivApi
import Submission.Work.GCBasics.DivBaseChange
import Submission.Work.GCBasics.ell_eq_of_linEquiv
import Submission.Work.GCBasics.linEquiv_eq_of_ell_eq_one
import Submission.Work.GCBasics.map_landsIn
import Submission.Work.SpecLin.Interface
import Submission.Work.Domain.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

variable {K : Type u} [Field K]

noncomputable section

/-- A `K`-scheme separated over `Spec K` is a separated scheme. -/
instance instSchemeIsSeparated {X : Sch K} [IsSeparated X.hom] : X.left.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← terminal.comp_from X.hom]
  infer_instance

variable {C : CurveBasics.Curve K} [SpecLin.DivBase C]

/-! ## The divisor `divOf (b p) - divOf (a p)` and the relation `Rel` -/

/-- The divisor of the difference: `divD symGeom a b p = divOf (b ∘ p) - divOf (a ∘ p)`,
a divisor on `C_F` for `p` an `F`-point of `X`.  Its degree is `m`. -/
def divD (symGeom : ∀ n, SpecLin.SymGeom C n)
    {X : Sch K} {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) : Dv C F :=
  (symGeom (r + m)).divOf (p ≫ b) - (symGeom r).divOf (p ≫ a)

/-- **The RESID relation.**  `Rel symGeom a b p y` says that the point `y` of `Sym^m C`
represents the class of the divisor `divOf (b p) - divOf (a p)`:
`divOf y + divOf (a p) ~ divOf (b p)`. -/
def Rel (symGeom : ∀ n, SpecLin.SymGeom C n)
    {X : Sch K} {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) (y : FPt (symGeom m).S F) : Prop :=
  LinEquiv C ((symGeom m).divOf y + (symGeom r).divOf (p ≫ a))
    ((symGeom (r + m)).divOf (p ≫ b))

/-- `Rel` in terms of `divD`: `y` represents the class of `divD symGeom a b p`. -/
theorem rel_iff {symGeom : ∀ n, SpecLin.SymGeom C n}
    {X : Sch K} {r m : ℕ} {a : X ⟶ (symGeom r).S} {b : X ⟶ (symGeom (r + m)).S}
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) (y : FPt (symGeom m).S F) :
    Rel symGeom a b p y ↔ LinEquiv C ((symGeom m).divOf y) (divD symGeom a b p) := by
  rw [Rel, divD,
    ← LinEquiv.sub_iff (D := (symGeom m).divOf y + (symGeom r).divOf (p ≫ a))
      (D' := (symGeom (r + m)).divOf (p ≫ b)) (E := (symGeom r).divOf (p ≫ a))]
  rw [add_sub_cancel_right]

/-- **Uniqueness of the representative when `ℓ = 1`.**  Two points of `Sym^m C` with linearly
equivalent divisors, one of which has `ℓ = 1`, are equal. -/
theorem divOf_eq_of_linEquiv_of_ell_eq_one
    {symGeom : ∀ n, SpecLin.SymGeom C n} {m : ℕ} {F : Type u} [Field F] [Algebra K F]
    {y z : FPt (symGeom m).S F}
    (h : LinEquiv C ((symGeom m).divOf y) ((symGeom m).divOf z))
    (h1 : ell C ((symGeom m).divOf y) = 1) : y = z :=
  (symGeom m).divOf_injective _ _
    (linEquiv_eq_of_ell_eq_one ((symGeom m).divOf_isEffective y) h1
      ((symGeom m).divOf_isEffective z) h)

/-! ## Addition of symmetric powers

`SpecLin.SymGeom` does not record the addition `Sym^r × Sym^m ⟶ Sym^{r+m}` (that is area
`SY`'s `addMap`, a field of `Work.GroupChunk.Input`).  RESID needs it, so it is taken here as
a named hypothesis, in exactly the form in which `Work.GroupChunk.Input` declares it. -/

/-- Addition of a point of `Sym^r C` and a point of `Sym^m C`. -/
def addMor (symGeom : ∀ n, SpecLin.SymGeom C n)
    (addMap : ∀ m n, (symGeom m).S ⊗ (symGeom n).S ⟶ (symGeom (m + n)).S)
    {X : Sch K} {r m : ℕ} (u : X ⟶ (symGeom r).S) (y : X ⟶ (symGeom m).S) :
    X ⟶ (symGeom (r + m)).S :=
  CartesianMonoidalCategory.liftEquiv (u, y) ≫ addMap r m

/-- `divOf` of the sum of two points is the sum of the divisors (the hypothesis
`addMap_divOf` is the field of the same name of `Work.GroupChunk.Input`). -/
theorem addMor_divOf {symGeom : ∀ n, SpecLin.SymGeom C n}
    {addMap : ∀ m n, (symGeom m).S ⊗ (symGeom n).S ⟶ (symGeom (m + n)).S}
    (addMap_divOf : ∀ m n {X : Sch K} (u : X ⟶ (symGeom m).S) (v : X ⟶ (symGeom n).S)
      {F : Type u} [Field F] [Algebra K F] (p : FPt X F),
      (symGeom (m + n)).divOf ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ addMap m n)
        = (symGeom m).divOf (p ≫ u) + (symGeom n).divOf (p ≫ v))
    {X : Sch K} {r m : ℕ} (u : X ⟶ (symGeom r).S) (y : X ⟶ (symGeom m).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) :
    (symGeom (r + m)).divOf (p ≫ addMor symGeom addMap u y)
      = (symGeom r).divOf (p ≫ u) + (symGeom m).divOf (p ≫ y) := by
  simpa only [addMor, Category.assoc] using addMap_divOf r m u y p

/-! ## The value of a rational map at a point of its domain -/

/-- **The value of a rational map at a point of its domain** (this is
`Work.GroupChunk.value`, reproduced here so that area `DM` is independent of area `GC`).
If `p : Spec F ⟶ X` is a point of a `K`-scheme `X` whose closed point lands in the domain of
`σ : X ⤏ Y`, then `p` factors through `σ.domain` and the composite with `σ` is a point of
`Y`. -/
def valueOf {X Y : Sch K} (hred : IsReduced X.left)
    (hsep : IsSeparated Y.hom) (σ : X.left ⤏ Y.left) (hσ : σ.IsOver (Spec (CommRingCat.of K)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) (hp : RPt.LandsIn p σ.domain) :
    FPt Y F := by
  haveI : IsReduced X.left := hred
  haveI : IsSeparated Y.hom := hsep
  haveI : Y.left.IsSeparated := inferInstance
  have hdom : σ.toPartialMap.domain = σ.domain := rfl
  have hp' : RPt.LandsIn p σ.toPartialMap.domain := hdom.symm ▸ hp
  let q : RPt (Opens.toOver σ.toPartialMap.domain) F :=
    Classical.choose (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp')
  have hq : q ≫ Opens.ιOver σ.toPartialMap.domain = p :=
    (Classical.choose_spec
      (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp')).1
  have h1 : (σ.toPartialMap).toRationalMap.IsOver (Spec (CommRingCat.of K)) := by
    rw [Scheme.RationalMap.toRationalMap_toPartialMap]
    exact hσ
  have h2 : (σ.toPartialMap).IsOver (Spec (CommRingCat.of K)) :=
    (Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
      (S := Spec (CommRingCat.of K))).mp h1
  have h3 : (σ.toPartialMap).hom ≫ Y.hom = (σ.toPartialMap).domain.ι ≫ X.hom := h2.1
  have hq' : q.left ≫ (σ.toPartialMap).domain.ι = p.left := by
    have h := congrArg Over.Hom.left hq
    simpa [Opens.ιOver_left] using h
  refine Over.homMk (q.left ≫ (σ.toPartialMap).hom) ?_
  rw [Category.assoc, h3, ← Category.assoc, hq']
  exact Over.Hom.w p

/-! ## The RESID specification -/

/-- **RESID.**  A rational map `σ : X ⤏ Sym^m C` computing the effective representative of
the class of `divOf (b p) - divOf (a p)`, with

* VALUE: at every field point of `X` in the domain of `σ`, `σ(p)` represents the class;
* DEFINED: at every point `x` of `X` where `ℓ` of that class is `1`, `σ` is defined.

This is `Work.GroupChunk.Resid` with the value `Work.Domain.Resid.valueOf` in place of
`Work.GroupChunk.value`; the two are definitionally equal. -/
structure ResidMap (symGeom : ∀ n, SpecLin.SymGeom C n) {X : Sch K}
    (hred : IsReduced X.left) {r m : ℕ} (hsep : IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (σ : X.left ⤏ (symGeom m).S.left) : Prop where
  /-- `σ` is a morphism over `K`. -/
  isOver : σ.IsOver (Spec (CommRingCat.of K))
  /-- VALUE. -/
  value : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp : RPt.LandsIn p σ.domain),
    Rel symGeom a b p (valueOf hred hsep σ isOver p hp)
  /-- DEFINED. -/
  mem_domain : ∀ (x : X.left),
    ell C (divD symGeom a b (resPt X x)) = 1 → x ∈ σ.domain

end

end Work.Domain.Resid
