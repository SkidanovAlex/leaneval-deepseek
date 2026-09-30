/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL, layer 4: the sum map on divisors

This file upgrades the pencil-based key lemma of `Submission/Work/KeyLemma/Pencil.lean`
(which is stated for *models*, i.e. multisets of `k`-points) to a statement about effective
divisors, which is the form in which the Jacobian development consumes it:

> `Σ f : {effective divisors of degree n which are split over k} ⟶ A(k)` is constant on
> linear equivalence classes.

The passage from multisets to divisors uses `SumDiv.toDiv_injective`: a `k`-point of a
curve is determined by the closed point which is its image
(`Work.KeyLemma.Curve.placeOfPoint_injective`), so a split effective divisor has a *unique*
model and the sum of the images of its points is well defined.

## Main definitions

* `Work.KeyLemma.Curve.HasModel`: the assertion that an effective divisor is the divisor of
  a multiset of `k`-points (`HasModel C D ↔ D.IsEffective ∧ IsSplit C D`).
* `Work.KeyLemma.Curve.sumMapOfModel`: the sum `Σ f(D) ∈ A(k)`, defined by choosing a model.

## Main results

* `Work.KeyLemma.Curve.sumMapOfModel_add`: `Σ f(D + E) = Σ f(D) · Σ f(E)` (the lead's item (a)).
* `Work.KeyLemma.Curve.sumMapOfModel_congr`: `Σ f(D)` does not depend on the chosen model.
* `Work.KeyLemma.Curve.sumMapOfModel_eq_of_linEquiv`: **the key lemma for divisors**.
* `Work.KeyLemma.Curve.EffDiv.sumMapOfModel_eq_of_linEquiv`: the statement of the blueprint for
  effective divisors of degree `n`.

## Not yet available

Compatibility of `sumMapOfModel` with base change of the base field (the lead's item (b)) needs the
base change of divisors along a field extension `L/k` (a map `Div C ⟶ Div (C_L)` compatible
with `toDiv`), which is area `CB`'s item 6 and not yet in the workspace; see `NOTES.md`.
The point-level half of it, `Curve.baseChangePoint`, is available below.
-/
import Submission.Work.KeyLemma.Pencil
import Submission.Work.KeyLemma.Sum.isSplit_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-! ## Models -/

/-- An effective divisor of `C` *admits a model* if it is the divisor of a multiset of
`k`-points of `C`.  Equivalently: it is effective and split over `k`
(`Work.KeyLemma.Curve.isSplit_iff`). -/
abbrev HasModel (C : Curve k) (D : C.Div) : Prop := ∃ s : SumDiv C, SumDiv.toDiv C s = D

theorem hasModel_toDiv (C : Curve k) (s : SumDiv C) : HasModel C (SumDiv.toDiv C s) :=
  ⟨s, rfl⟩

theorem HasModel.isEffective {C : Curve k} {D : C.Div} (h : HasModel C D) :
    D.IsEffective := by
  obtain ⟨s, rfl⟩ := h
  exact SumDiv.toDiv_isEffective C s

/-- An *effective* divisor has a model if and only if it is split over `k`
(`Work.KeyLemma.Sum.isSplit_iff`). -/
theorem hasModel_iff {C : Curve k} {D : C.Div} (hD : D.IsEffective) :
    HasModel C D ↔ IsSplit C D :=
  (Work.KeyLemma.Sum.isSplit_iff C hD).symm

theorem IsSplit.hasModel {C : Curve k} {D : C.Div} (hD : D.IsEffective) (h : IsSplit C D) :
    HasModel C D :=
  (hasModel_iff hD).mpr h

theorem HasModel.isSplit {C : Curve k} {D : C.Div} (h : HasModel C D) : IsSplit C D :=
  (hasModel_iff h.isEffective).mp h

/-! ## The sum of a split effective divisor -/

/-- The sum of the images in `A` of the points of a split effective divisor `D` of `C`:
the sum of the images of the points of a model of `D` (the result does not depend on the
model, see `sumMapOfModel_congr`). -/
noncomputable def sumMapOfModel (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (D : C.Div) (hD : HasModel C D) : Pt k A :=
  SumDiv.sumOfPoints C f (Classical.choose hD)

/-- The chosen model of `D` really has divisor `D`. -/
theorem sumMapOfModel_def (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) {D : C.Div} (hD : HasModel C D) :
    SumDiv.toDiv C (Classical.choose hD) = D :=
  Classical.choose_spec hD

/-- The sum `Σ f(D)` of a split effective divisor `D`, with the splitness hypothesis
spelled out as effectivity plus `IsSplit`. -/
noncomputable def sumMapOfIsSplit (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (D : C.Div) (hD : D.IsEffective)
    (h : IsSplit C D) : Pt k A :=
  sumMapOfModel C f D (h.hasModel hD)

/-- The sum does not depend on the chosen model. -/
theorem sumMapOfModel_congr (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (hinj : Function.Injective (SumDiv.toDiv C))
    {D : C.Div} (hD hD' : HasModel C D) : sumMapOfModel C f D hD = sumMapOfModel C f D hD' := by
  unfold sumMapOfModel
  refine SumDiv.sumOfPoints_of_toDiv_eq C f hinj ?_
  calc SumDiv.toDiv C (Classical.choose hD) = D := sumMapOfModel_def C f hD
    _ = SumDiv.toDiv C (Classical.choose hD') := (sumMapOfModel_def C f hD').symm

theorem sumOfPoints_choose_eq (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (hinj : Function.Injective (SumDiv.toDiv C))
    {D : C.Div} (hD hD' : HasModel C D) :
    SumDiv.sumOfPoints C f (Classical.choose hD) =
      SumDiv.sumOfPoints C f (Classical.choose hD') :=
  sumMapOfModel_congr C f hinj hD hD'

/-- **Additivity of the sum map.** -/
theorem sumMapOfModel_add (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsCommMonObj A] (f : C.toOver ⟶ A) (hinj : Function.Injective (SumDiv.toDiv C))
    {D E : C.Div} (hD : HasModel C D) (hE : HasModel C E) (hDE : HasModel C (D + E)) :
    sumMapOfModel C f (D + E) hDE = sumMapOfModel C f D hD * sumMapOfModel C f E hE := by
  have hsum : SumDiv.toDiv C (Classical.choose hD + Classical.choose hE) = D + E := by
    calc SumDiv.toDiv C (Classical.choose hD + Classical.choose hE)
        = SumDiv.toDiv C (Classical.choose hD) + SumDiv.toDiv C (Classical.choose hE) :=
          SumDiv.toDiv_add C _ _
      _ = D + E := by rw [sumMapOfModel_def C f hD, sumMapOfModel_def C f hE]
  have hmodel : Classical.choose hDE = Classical.choose hD + Classical.choose hE :=
    hinj (by
      calc SumDiv.toDiv C (Classical.choose hDE) = D + E := sumMapOfModel_def C f hDE
        _ = SumDiv.toDiv C (Classical.choose hD + Classical.choose hE) := hsum.symm)
  unfold sumMapOfModel
  rw [hmodel, SumDiv.sumOfPoints_add]

/-- **The key lemma for divisors.**  `Σ f` is constant on linear equivalence classes of
split effective divisors. -/
theorem sumMapOfModel_eq_of_linEquiv (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) (K : KeyLemmaInput C A f)
    {D D' : C.Div} (hD : HasModel C D) (hD' : HasModel C D') (h : LinEquiv C D D') :
    sumMapOfModel C f D hD = sumMapOfModel C f D' hD' := by
  obtain ⟨h, hh, hdiv⟩ := h
  have hdiv' : C.div h = SumDiv.toDiv C (Classical.choose hD) -
      SumDiv.toDiv C (Classical.choose hD') := by
    rw [sumMapOfModel_def C f hD, sumMapOfModel_def C f hD']
    exact hdiv <;> assumption
  unfold sumMapOfModel
  exact sumOfPoints_eq_of_linEquiv C f K hh hdiv'

namespace EffDiv

variable {C : Curve k} {n : ℕ}

/-- **The key lemma, in the form of the blueprint**: for effective divisors of degree `n`
which are split over `k`, the sum `Σ f` is constant on linear equivalence classes. -/
theorem sumMapOfModel_eq_of_linEquiv {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) (K : KeyLemmaInput C A f)
    (D D' : EffDiv C n) (hD : HasModel C D.1) (hD' : HasModel C D'.1)
    (h : LinEquiv D D') : sumMapOfModel C f D.1 hD = sumMapOfModel C f D'.1 hD' :=
  Curve.sumMapOfModel_eq_of_linEquiv C f K hD hD' h

end EffDiv

end

end Curve

end Work.KeyLemma
