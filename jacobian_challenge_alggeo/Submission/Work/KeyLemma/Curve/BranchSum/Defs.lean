/-
# The branches of the pencil at a zero of `h`: definitions

This file collects the definitions and the immediate consequences that the branch-sum
statement `Work.KeyLemma.Curve.exists_branch_sum_fixed` is built from.

Setting: `k` a field, `C` a curve, `h ∈ K(C)`, `K := k(h) ⊆ E := K(C)`, `N` a field which is a
`K`-algebra and a `k`-algebra compatibly, `R'` a `k`-algebra which is a valuation ring of `N`
(`IsFractionRing R' N`).

* `conjPtOverC C h σ : Spec N ⟶ C` is the conjugate point attached to a `K`-embedding
  `σ : E →ₐ[K] N`, as a morphism over `Spec k`;
* `exists_branch C h σ` produces an extension `Spec R' ⟶ C` of `conjPtOverC C h σ`, and
  `branch` is the chosen such extension;
* `branch_unique` is its uniqueness (separatedness of `C`).
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.BranchSum.Valuative
import Submission.Work.SpecLin.Setup.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma.Curve

open Work.SpecLin

noncomputable section

variable {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (h : C.functionField)
  {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
  [IsScalarTower k ↥(baseField C h) N]

/-- The conjugate `N`-point of `C` attached to a `K`-embedding `σ : E →ₐ[K] N`, as a morphism
over `Spec k`. -/
def conjPtOverC (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) : specOver N ⟶ C.toOver :=
  Over.homMk (conjPt C h N σ) (by
    dsimp only [conjPt, genericPt, specOver]
    rw [Category.assoc, Work.CurveBasics.Curve.fromSpecStalk_genericPoint_comp_hom,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact (AlgHom.commutes σ x).trans (IsScalarTower.algebraMap_apply k ↥(baseField C h) N x).symm)

@[simp]
theorem conjPtOverC_left (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) :
    (conjPtOverC C h σ).left = conjPt C h N σ := rfl

/-- **Existence of the branch**: the conjugate `N`-point `conjPtOverC C h σ` extends to an
`R'`-point of `C`, for `R'` a valuation ring of `N`.  This is the valuative criterion for
properness of `C`. -/
theorem exists_branch {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Algebra k R'] [Algebra R' N] [IsScalarTower k R' N] [IsFractionRing R' N]
    (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) :
    ∃ g : specOf (K := k) R' ⟶ C.toOver,
      specOfMap (K := k) (IsScalarTower.toAlgHom k R' N) ≫ g = conjPtOverC C h σ := by
  obtain ⟨ρ, hρ1, hρ2⟩ := Work.KeyLemma.Curve.exists_extension_of_proper_field
    (k := k) (R := R') (K := N) (X := C.toOver)
    (conjPt C h N σ) (conjPtOverC C h σ).w
  refine ⟨Over.homMk ρ hρ1, ?_⟩
  apply Over.OverMorphism.ext
  simpa only [Over.comp_left, Over.homMk_left, conjPtOverC_left, Work.SpecLin.specOfMap,
    Work.SpecLin.specOfMapHom, IsScalarTower.toAlgHom] using hρ2

/-- **Uniqueness of the branch** (separatedness of `C`): two `R'`-points of `C` with the same
generic fibre over `N` agree. -/
theorem branch_unique {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Algebra k R'] [Algebra R' N] [IsScalarTower k R' N] [IsFractionRing R' N]
    {g g' : specOf (K := k) R' ⟶ C.toOver}
    (hgg' : specOfMap (K := k) (IsScalarTower.toAlgHom k R' N) ≫ g
      = specOfMap (K := k) (IsScalarTower.toAlgHom k R' N) ≫ g') : g = g' := by
  apply Over.OverMorphism.ext
  refine Work.KeyLemma.Curve.eq_of_generic_eq (k := k) (R := R') (K := N) (X := C.toOver)
    (u := g.left) (v := g'.left) g.w g'.w ?_
  exact congrArg Over.Hom.left hgg'

/-- The chosen branch of the pencil at `σ`. -/
def branch {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Algebra k R'] [Algebra R' N] [IsScalarTower k R' N] [IsFractionRing R' N]
    (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) : specOf (K := k) R' ⟶ C.toOver :=
  Classical.choose (exists_branch C h σ)

theorem branch_spec {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Algebra k R'] [Algebra R' N] [IsScalarTower k R' N] [IsFractionRing R' N]
    (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) :
    specOfMap (K := k) (IsScalarTower.toAlgHom k R' N) ≫ branch (C := C) (h := h) σ
      = conjPtOverC C h σ :=
  Classical.choose_spec (exists_branch (C := C) (h := h) (R' := R') σ)

end

end Work.KeyLemma.Curve
