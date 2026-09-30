/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): API for the value of a rational map at a point of its domain

The two lemmas

* `Work.Domain.Resid.valueOf_left_eq`: the value of a rational map at a point of its domain is
  computed by *any* lift of that point through the domain (the lift produced by
  `Work.GCBasics.RPt.factor_of_closed_landsIn` is unique), and
* `Work.Domain.Resid.valueOf_proof_irrel`: the value does not depend on the proof that the
  point lies in the domain,

are the bookkeeping lemmas by which the VALUE theorem `Work.Domain.Resid.residMap_value` is
assembled from the residue-point relation `Work.Domain.Resid.rel_resPt`.
-/
import Mathlib
import Submission.Work.Domain.Resid.Setup

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

noncomputable section

variable {K : Type u} [Field K]

/-- The value of a rational map is computed by any lift of its argument. -/
theorem valueOf_left_eq {X Y : Sch K} (hred : IsReduced X.left)
    (hsep : IsSeparated Y.hom) (σ : X.left ⤏ Y.left)
    (hσ : σ.IsOver (Spec (CommRingCat.of K)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp : RPt.LandsIn p σ.domain)
    (q : RPt (Opens.toOver σ.toPartialMap.domain) F)
    (hq : q ≫ Opens.ιOver σ.toPartialMap.domain = p) :
    (valueOf hred hsep σ hσ p hp).left = q.left ≫ σ.toPartialMap.hom := by
  haveI : IsReduced X.left := hred
  haveI : IsSeparated Y.hom := hsep
  haveI : Y.left.IsSeparated := inferInstance
  have hdom : σ.toPartialMap.domain = σ.domain := rfl
  have hp' : RPt.LandsIn p σ.toPartialMap.domain := hdom.symm ▸ hp
  have hspec := Classical.choose_spec (RPt.factor_of_closed_landsIn (K := K)
    σ.toPartialMap.domain p hp')
  have huniq : Classical.choose (RPt.factor_of_closed_landsIn (K := K)
      σ.toPartialMap.domain p hp') = q := (hspec.2 q hq).symm
  rw [valueOf]
  simp only [Over.homMk_left]
  rw [huniq]

/-- The value of a rational map does not depend on the proof that the point lies in the
domain. -/
theorem valueOf_proof_irrel {X Y : Sch K} (hred : IsReduced X.left)
    (hsep : IsSeparated Y.hom) (σ : X.left ⤏ Y.left)
    (hσ : σ.IsOver (Spec (CommRingCat.of K)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp1 hp2 : RPt.LandsIn p σ.domain) :
    valueOf hred hsep σ hσ p hp1 = valueOf hred hsep σ hσ p hp2 := by
  obtain ⟨q, hq, -⟩ := RPt.factor_of_closed_landsIn σ.toPartialMap.domain p
    (show RPt.LandsIn p σ.toPartialMap.domain from hp1)
  apply Over.OverMorphism.ext
  exact (valueOf_left_eq hred hsep σ hσ p hp1 q hq).trans
    (valueOf_left_eq hred hsep σ hσ p hp2 q hq).symm

end

end Work.Domain.Resid
