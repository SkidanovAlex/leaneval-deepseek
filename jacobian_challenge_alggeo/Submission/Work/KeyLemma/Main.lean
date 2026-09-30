/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: the key lemma, user-facing forms

This file assembles the two geometric inputs into `Curve.KeyLemmaInput` and states the key
lemma in the forms in which other areas consume it.

The two inputs (see `Submission/Work/KeyLemma/Pencil.lean` and `NOTES.md`):

* `Curve.PencilGeometric C f`: the fibrewise sum of a pencil is the value of a morphism
  `ℙ¹ ⟶ A` at points (area `SY` + the specialisation at `t = 0, ∞`);
* `Curve.P1Const k`: `P1CONST`, every morphism `ℙ¹ ⟶ B` into a proper group scheme is
  constant (area `AV`, `Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine`).

Everything else -- including the injectivity of `SumDiv.toDiv`
(`Work.KeyLemma.Sum.toDiv_injective`, i.e. a `k`-point of a curve is determined by its image
place) -- is proved in this area.  The base change of the base field (the lead's item (b)) is
in `Submission/Work/KeyLemma/BaseChange/SumBaseChange.lean`.
-/
import Submission.Work.KeyLemma.SumMap
import Submission.Work.KeyLemma.BaseChange
import Submission.Work.KeyLemma.Sum.toDiv_injective
import Submission.Work.KeyLemma.Sum.deg_toDiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
-- Mathlib's transport of (commutative) group objects along a monoidal functor:
open scoped CategoryTheory.Obj

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The two geometric inputs of the key lemma, assembled into a `Curve.KeyLemmaInput`
(the injectivity of `toDiv` is a theorem of this area). -/
theorem keyLemmaInput_of_pencil (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A)
    (hgeo : PencilGeometric C f) : KeyLemmaInput C A f :=
  ⟨Work.KeyLemma.Sum.toDiv_injective C, hgeo⟩

/-- **The key lemma `KL`**, with the two geometric inputs as the only hypotheses: for
effective divisors `D`, `D'` of a curve which are split over `k` and linearly equivalent,
the sums of the images of their points in an abelian variety `A` agree. -/
theorem linEquiv_sum_eq (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A)
    (hgeo : PencilGeometric C f) {D D' : C.Div}
    (hD : D.IsEffective) (hD' : D'.IsEffective) (hs : IsSplit C D) (hs' : IsSplit C D')
    (h : LinEquiv C D D') :
    sumMapOfIsSplit C f D hD hs = sumMapOfIsSplit C f D' hD' hs' := by
  rw [sumMapOfIsSplit, sumMapOfIsSplit]
  exact sumMapOfModel_eq_of_linEquiv C f (keyLemmaInput_of_pencil C f hgeo) _ _ h

/-- **The key lemma `KL`** for effective divisors of degree `n`, with the two geometric
inputs as the only hypotheses (this is blueprint item 6). -/
theorem EffDiv.linEquiv_sumMapOfModel_eq (C : Curve k) {A : Over (Spec (CommRingCat.of k))}
    [GrpObj A] [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A)
    (hgeo : PencilGeometric C f) {n : ℕ} (D D' : EffDiv C n)
    (hD : IsSplit C D.1) (hD' : IsSplit C D'.1) (h : EffDiv.LinEquiv D D') :
    sumMapOfIsSplit C f D.1 D.isEffective hD =
      sumMapOfIsSplit C f D'.1 D'.isEffective hD' :=
  linEquiv_sum_eq C f hgeo D.isEffective D'.isEffective hD hD' h

/-- A model of a split effective divisor of degree `n` has exactly `n` points (counted with
multiplicity): `SumDiv.deg` computes the degree. -/
theorem SumDiv.deg_eq_of_toDiv_eq {C : Curve k} {n : ℕ} (D : EffDiv C n)
    {s : SumDiv C} (hs : SumDiv.toDiv C s = D.1) : s.deg = n := by
  have h1 : C.deg (SumDiv.toDiv C s) = (s.deg : ℤ) := Work.KeyLemma.Sum.deg_toDiv C s
  rw [hs, D.deg_eq] at h1
  exact_mod_cast h1.symm

end

end Curve

end Work.KeyLemma
