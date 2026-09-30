/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: the key lemma of the Jacobian challenge, unconditional

`Work.KeyLemma.Curve.pencilGeometric` (`Submission/Work/KeyLemma/Curve/pencilGeometric.lean`)
proves the geometric input `Curve.PencilGeometric` for an arbitrary base field, so the key lemma
of the contract — blueprint items 1, 2, 3 and 6 — no longer has any geometric hypothesis: every
form of it is a theorem of this workspace, with the *symmetric-power interface* (`Curve.SymPow`,
`Curve.SymPow.BaseChange`, `Curve.IsSumMorphismBC`, area `SY`/`UP`) as its only remaining
hypotheses where the divisors are not split over the base field.

## Main results

* `Work.KeyLemma.Curve.keyLemmaInput`: the two inputs of the key lemma are theorems, so
  `Curve.KeyLemmaInput C A f` is *inhabited*.
* `Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond`: the key lemma in model form
  (`Σ f(s) = Σ f(s')` for multisets of `k`-points with `div h = toDiv s - toDiv s'`).
* `Work.KeyLemma.Curve.linEquiv_sum_eq_uncond`: the key lemma for effective divisors split over
  the base field.
* `Work.KeyLemma.Curve.EffDiv.linEquiv_sumMapOfModel_eq_uncond`: blueprint item 6 — the split
  sum map `EffDiv_n(C) → A(k)` is constant on linear equivalence classes.
* `Work.KeyLemma.Curve.sumMapPow_eq_of_linEquiv_uncond` (`Unconditional.lean`): the same for the
  *total* sum map `Σ f : EffDiv_n(C) → A(k)`, i.e. with no splitting hypothesis, from the
  symmetric-power interface of `SY`/`UP`.
-/
import Submission.Work.KeyLemma.Curve.pencilGeometric
import Submission.Work.KeyLemma.Main
import Submission.Work.KeyLemma.Unconditional

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- **The key lemma has no remaining geometric input**: both fields of `Curve.KeyLemmaInput` are
theorems — `toDiv_injective` (`Work.KeyLemma.Sum.toDiv_injective`) and `pencil_geometric`
(`Work.KeyLemma.Curve.pencilGeometric`). -/
theorem keyLemmaInput (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) : KeyLemmaInput C A f :=
  ⟨Work.KeyLemma.Sum.toDiv_injective C, pencilGeometric C f⟩

/-- **The key lemma `KL` in model form, unconditional.**  Let `s`, `s'` be multisets of
`k`-points of a curve `C` whose effective divisors are linearly equivalent, `div h = toDiv s -
toDiv s'` for a nonzero rational function `h`.  Then the sums of the images of the points of `s`
and of `s'` in the commutative group `A(k)` of `k`-points of a proper commutative group scheme
`A` agree.  No geometric hypothesis remains. -/
theorem sumOfPoints_eq_of_linEquiv_uncond (C : Curve k)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsProper A.hom] [IsCommMonObj A]
    (f : C.toOver ⟶ A) {s s' : SumDiv C} {h : C.functionField} (hh : h ≠ 0)
    (hdiv : C.div h = SumDiv.toDiv C s - SumDiv.toDiv C s') :
    SumDiv.sumOfPoints C f s = SumDiv.sumOfPoints C f s' :=
  sumOfPoints_eq_of_linEquiv C f (keyLemmaInput C f) hh hdiv

/-- **The key lemma for effective divisors split over the base field, unconditional.** -/
theorem linEquiv_sum_eq_uncond (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) {D D' : C.Div}
    (hD : D.IsEffective) (hD' : D'.IsEffective) (hs : IsSplit C D) (hs' : IsSplit C D')
    (h : LinEquiv C D D') :
    sumMapOfIsSplit C f D hD hs = sumMapOfIsSplit C f D' hD' hs' :=
  linEquiv_sum_eq C f (pencilGeometric C f) hD hD' hs hs' h

/-- **Blueprint item 6, unconditional**: the sum map `Σ f : EffDiv_n(C) → A(k)` of a projective
curve over a *general* field — restricted to the divisors which are split over `k` — is constant
on the linear equivalence classes of effective divisors of degree `n`. -/
theorem EffDiv.linEquiv_sumMapOfModel_eq_uncond (C : Curve k)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsProper A.hom] [IsCommMonObj A]
    (f : C.toOver ⟶ A) {n : ℕ} (D D' : EffDiv C n) (hD : IsSplit C D.1)
    (hD' : IsSplit C D'.1) (h : EffDiv.LinEquiv D D') :
    sumMapOfIsSplit C f D.1 D.isEffective hD =
      sumMapOfIsSplit C f D'.1 D'.isEffective hD' :=
  EffDiv.linEquiv_sumMapOfModel_eq C f (pencilGeometric C f) D D' hD hD' h

end

end Curve

end Work.KeyLemma
