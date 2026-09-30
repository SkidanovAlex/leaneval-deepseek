/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: the key lemma with no remaining geometric input

`Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed`
(`Submission/Work/KeyLemma/Curve/pencilGeometric_of_isAlgClosed.lean`) proves the geometric input
`Curve.PencilGeometric` of the key lemma over an algebraically closed field.  The key lemma is
applied through the base-changed form `Curve.PencilGeometricBaseChange L f`, and the equality
obtained over an algebraically closed `L` descends to `k` by `Curve.Pt.baseChange_injective`;
hence the residual input is *gone* and the key lemma for the total sum map is a theorem.

## Main results

* `Work.KeyLemma.Curve.sumMapPow_eq_of_linEquiv_uncond`: **the key lemma for the total sum map**
  `Σ f : EffDiv_n(C) → A(k)` is constant on linear equivalence classes, with no geometric
  hypothesis beyond the symmetric-power interface: hypotheses are `Curve.SymPow C n`, its
  `BaseChange` to an algebraically closed `L`, and `Curve.IsSumMorphismBC`.
-/
import Submission.Work.KeyLemma.Curve.sumMapPow_eq_of_linEquiv
import Submission.Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed

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

/-- **The key lemma `KL` for the total sum map, unconditional.**  Let `C` be a curve over a
field `k`, `A` a commutative group scheme over `k`, `f : C ⟶ A`, `G = Sym^n C` a symmetric
power, `Φ : G.S ⟶ A` a sum morphism for `f`, and `bc` its naturality under a base change to an
algebraically closed field `L`.  Then the sum map `Σ f : EffDiv C n → Pt k A` is constant on the
linear equivalence classes of effective divisors of degree `n`.

The only remaining hypotheses are the symmetric-power interface of area `SY` (`Curve.SymPow`,
its `BaseChange`, and `Curve.IsSumMorphismBC`), i.e. the construction of the sum morphism; the
*pencil* geometry is now a theorem (`Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed`). -/
theorem sumMapPow_eq_of_linEquiv_uncond {C : Curve k} {n : ℕ}
    (G : SymPow C n) {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] (f : C.toOver ⟶ A) {Φ : G.S ⟶ A}
    {L : Type u} [Field L] [Algebra k L] [IsAlgClosed L] (bc : G.BaseChange L)
    (hΦL : IsSumMorphismBC G Φ bc f) (D D' : EffDiv C n) (h : EffDiv.LinEquiv D D') :
    sumMap G Φ D = sumMap G Φ D' := by
  haveI : IsProper ((baseChangeFunctor k L).obj A).hom := by
    change IsProper (pullback.snd A.hom (Work.CurveBasics.Curve.specMap k L))
    infer_instance
  exact sumMapPow_eq_of_linEquiv G f bc hΦL
    (pencilGeometric_of_isAlgClosed (Curve.baseChange C L) ((baseChangeFunctor k L).map f))
    D D' h

end

end Curve

end Work.KeyLemma
