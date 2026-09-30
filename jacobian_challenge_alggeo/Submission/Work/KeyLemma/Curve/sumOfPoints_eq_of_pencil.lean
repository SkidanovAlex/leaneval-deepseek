/-
# The pencil case of the key lemma, over an algebraically closed field

`Work.KeyLemma.Curve.sumOfPoints_eq_of_pencil` is the statement that for a curve `C` over an
algebraically closed field `k`, a nonzero nonconstant rational function `h ∈ K(C)`, a morphism
`f : C ⟶ A` into a proper commutative group scheme, and multisets `s₀`, `s₁` of `k`-points of
`C` presenting the divisors of zeros and of poles of `h`, the sums of the images of the points
of `s₀` and of `s₁` in the group `A(k)` agree.

## Status of the proof

This statement is the *pencil case of the key lemma* `KL` of the Jacobian challenge, and (by the
equivalence noted in `Submission/Work/KeyLemma/NOTES.md`) it is equivalent to the residual
geometric input `Work.KeyLemma.Curve.PencilGeometric` over an algebraically closed field.

Everything except that single input is proved in this workspace:

* `Work.KeyLemma.Sum.toDiv_injective` (a `k`-point of a curve is determined by its image
  place) gives the `toDiv_injective` field of `KeyLemmaInput`;
* `Work.KeyLemma.Curve.pencil_eq` turns `PencilGeometric` into the asserted equality, using
  the *proved* rigidity statement `Work.KeyLemma.Curve.p1Const` (`P1CONST`).

The one remaining input is `Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed`
(`Submission/Work/KeyLemma/Curve/pencilGeometric_of_isAlgClosed.lean`), the "fibrewise sum of a
pencil is a morphism `ℙ¹ ⟶ A`" statement.  Its mathematical content is the classification of
the family of fibres of a pencil by a morphism `ℙ¹ ⟶ Sym^m C` (relative effective divisors), or
equivalently the specialisation of the ordered fibres of the pencil.  Pieces of the two known
routes (see `NOTES_pencil.md` next to this file, and `NOTES.md` Addendum 3) that are **proved**
in this workspace:

* `Work.KeyLemma.Curve.surjective_toP1` -- a nonconstant morphism from a curve to `ℙ¹` is
  surjective (so every fibre is nonempty);
* `Work.KeyLemma.Curve.finite_flat_toP1` -- such a morphism is finite and flat, so the fibres
  are finite of constant total degree `m = [K(C) : k(h)]` (the degree bookkeeping behind the
  multiplicities);
* `Work.KeyLemma.Curve.extends_of_open_p1` -- a morphism from a nonempty open subscheme of
  `ℙ¹` into a proper `k`-scheme extends to `ℙ¹` (the extension step of the fibrewise sum map);
* `Work.Descent.galoisDescent_point` -- Galois descent of points of a separated scheme
  (the descent step of the "rational map" route).

What remains is the identification of the values of the fibrewise sum morphism at the ramified
ends `0`, `∞` with `Σ f(div₀ h)`, `Σ f(div_∞ h)`: see `NOTES_pencil.md`, §3 -- this is the
piece that still has to be built, and it is the substance of the input below.
-/
import Mathlib
import Submission.Work.KeyLemma.Pencil
import Submission.Work.KeyLemma.Curve.PencilMap
import Submission.Work.KeyLemma.Curve.pencil_general_of_separable
import Submission.Work.KeyLemma.Curve.sumOfPoints_eq_of_separable
import Submission.Work.KeyLemma.Sum.toDiv_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.KeyLemma.Curve

theorem sumOfPoints_eq_of_pencil {k : Type u} [Field k] [IsAlgClosed k]
    {C : Work.CurveBasics.Curve k}
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] [AlgebraicGeometry.IsProper A.hom]
    (f : C.toOver ⟶ A) {h : C.functionField} (hh : h ≠ 0)
    (hnc : ¬ Work.KeyLemma.Curve.IsConstant C h)
    (s₀ s₁ : Work.KeyLemma.Curve.SumDiv C)
    (hs₀ : Work.KeyLemma.Curve.SumDiv.toDiv C s₀ = Work.KeyLemma.Curve.posPart C h)
    (hs₁ : Work.KeyLemma.Curve.SumDiv.toDiv C s₁ = Work.KeyLemma.Curve.negPart C h) :
    Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₀ =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₁ := by
  exact Work.KeyLemma.Curve.pencil_general_of_separable (k := k) (C := C) (A := A) f
    (fun h hh hnc hsep s₀ s₁ hs₀ hs₁ =>
      Work.KeyLemma.Curve.sumOfPoints_eq_of_separable (C := C) (A := A) f
        h hh hnc hsep s₀ s₁ hs₀ hs₁)
    h hh hnc s₀ s₁ hs₀ hs₁

end Work.KeyLemma.Curve
