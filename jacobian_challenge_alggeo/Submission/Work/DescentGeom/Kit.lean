/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Basic
import Submission.Work.Descent.isGaloisQuotient_of_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the generic descent toolkit

The lemmas of this file are generic statements about the base-change functor `bcFun k k'`, the
Galois action `Work.Descent.galAct` and the projection `bcπ`, used by the geometric half of §3.7 of
`NOTES_LEAD_jacobian_GC.md`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

namespace Work.DescentGeom

noncomputable section

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- **The categorical quotient statement holds for an *arbitrary* `k`-scheme.**  The hypotheses
`IsSeparated`/`LocallyOfFiniteType` of `Work.Descent.baseChange_isQuotient` are not needed: its
proof reduces to the affine case, which is unconditional. -/
theorem isGaloisQuotient [FiniteDimensional k k'] [IsGalois k k'] (X : Sch k) :
    Work.Descent.IsGaloisQuotient k k' X := by
  refine Work.Descent.isGaloisQuotient_of_affineOpens X ?_
  intro U hU
  haveI : IsAffine (Over.mk (U.ι ≫ X.hom)).left := hU
  exact Work.Descent.isGaloisQuotient_of_isAffine _

/-- **Descent of `Γ`-invariant morphisms**, with no separatedness/finite-type hypothesis on the
source: the form of `Work.Descent.desc_of_invariant` used throughout this area for sources such as
`J ⊗ J` and `J ⊗ J ⊗ J`. -/
theorem desc_of_invariant [FiniteDimensional k k'] [IsGalois k k'] (X Y : Sch k)
    (Φ : (bc k' X).left ⟶ Y.left)
    (hΦ : Φ ≫ Y.hom = (bc k' X).hom ≫ Work.Descent.specMap k k')
    (h : ∀ σ : Work.Descent.Gal k k', Work.Descent.galAct X σ ≫ Φ = Φ) :
    ∃! φ : X ⟶ Y, bcπ k' X ≫ φ.left = Φ :=
  isGaloisQuotient X Y Φ hΦ h

/-- **Naturality of the Galois action** (restatement of `Work.Descent.galAct_naturality`). -/
theorem galAct_naturality (X Y : Sch k) (u : X ⟶ Y) (σ : Work.Descent.Gal k k') :
    Work.Descent.galAct X σ ≫ ((bcFun k k').map u).left =
      ((bcFun k k').map u).left ≫ Work.Descent.galAct Y σ :=
  Work.Descent.galAct_naturality u σ

/-- **Naturality of the projection.** -/
theorem baseChangepi_naturality (X Y : Sch k) (u : X ⟶ Y) :
    ((bcFun k k').map u).left ≫ bcπ k' Y = bcπ k' X ≫ u.left :=
  Work.Descent.baseChange_map_fst' u

/-- The Galois action on the tensor unit is the identity, against the terminal comparison. -/
theorem galAct_terminal (σ : Work.Descent.Gal k k') :
    Work.Descent.galAct (𝟙_ (Sch k)) σ ≫
        (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom.left =
      (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom.left ≫ specGal σ := by
  rw [Over.preservesTerminalIso_pullback]
  exact Work.Descent.galAct_snd' (𝟙_ (Sch k)) σ

/-- **The Galois action on a product** is the twisted diagonal action on the two factors. -/
theorem galAct_prodComparison (X Y : Sch k) (σ : Work.Descent.Gal k k') :
    Work.Descent.galAct (X ⊗ Y) σ ≫
        (CartesianMonoidalCategory.prodComparisonIso (bcFun k k') X Y).hom.left =
      (CartesianMonoidalCategory.prodComparisonIso (bcFun k k') X Y).hom.left ≫
        galActProdMap (bc k' X) (bc k' Y) (galActK k' X) (galActK k' Y)
          (galActK_hom X) (galActK_hom Y) σ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, galActProdMap, CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison, Over.lift_left,
      pullback.lift_fst, pullback.lift_fst_assoc]
    exact Work.Descent.galAct_naturality (CartesianMonoidalCategory.fst X Y) σ
  · simp only [Category.assoc, galActProdMap, CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison, Over.lift_left,
      pullback.lift_snd, pullback.lift_snd_assoc]
    exact Work.Descent.galAct_naturality (CartesianMonoidalCategory.snd X Y) σ

/-- **The base change functor is faithful**: a `k`-morphism of `k`-schemes is determined by its
base change to `k'`.  (The extension is not even required to be finite or Galois.) -/
theorem map_injective (X Y : Sch k) :
    Function.Injective (fun u : X ⟶ Y => (bcFun k k').map u) := by
  intro u v h
  have h3 : ((bcFun k k').map u).left = ((bcFun k k').map v).left :=
    congrArg (fun w => Over.Hom.left w) h
  have h4 : bcπ k' X ≫ u.left = bcπ k' X ≫ v.left := by
    rw [← baseChangepi_naturality X Y u, ← baseChangepi_naturality X Y v, h3]
  exact Over.OverMorphism.ext ((cancel_epi (bcπ k' X)).mp h4)

end

end Work.DescentGeom
