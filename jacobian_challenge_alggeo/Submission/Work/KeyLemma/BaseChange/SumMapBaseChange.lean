/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: the divisor-level base change bridge, and `sumMapOfModel` under base change

The lead's item (b) for area `KL` at the level of *divisors*:

* `Work.KeyLemma.Curve.SumDiv.toDiv_baseChange`: the multiset-level base change of points agrees
  with CB's base change of divisors, `toDiv ∘ SumDiv.baseChange = Curve.divMap ∘ toDiv`
  (this is the "bridge" between the two presentations of a divisor).
* `Work.KeyLemma.Curve.sumMapOfModel_baseChange`: consequently `Σ f` commutes with base change of the
  base field, `sumMapOfModel (C_L) f_L (divMap D) = baseChange (sumMapOfModel C f D)`.

Both are unconditional: the three fibre facts over a `k`-rational point
(`Work.KeyLemma.BaseChange.proj_placeOfPoint_baseChange`,
`…placeOfPoint_baseChange_unique`, `…ramIdx_placeOfPoint_baseChange`) are proved in this area,
and CB provides `Curve.divMap` with `Curve.divMap_apply`.
-/
import Submission.Work.KeyLemma.BaseChange
import Submission.Work.KeyLemma.BaseChange.SumBaseChange
import Submission.Work.KeyLemma.Main
import Submission.Work.KeyLemma.BaseChange.proj_placeOfPoint_baseChange
import Submission.Work.KeyLemma.BaseChange.placeOfPoint_baseChange_unique
import Submission.Work.KeyLemma.BaseChange.ramIdx_placeOfPoint_baseChange
import Submission.Work.KeyLemma.BaseChange.toDiv_baseChange

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

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]

/-- **The bridge between the two presentations of a divisor**: base changing a multiset of
`k`-points and then taking its divisor agrees with base changing the divisor. -/
theorem SumDiv.toDiv_baseChange (C : Curve k) (s : SumDiv C) :
    SumDiv.toDiv (Curve.baseChange C L) (SumDiv.baseChange C L s) =
      Curve.divMap C L (SumDiv.toDiv C s) :=
  Work.KeyLemma.BaseChange.toDiv_baseChange C L s
    (fun p => Work.KeyLemma.BaseChange.proj_placeOfPoint_baseChange C L p)
    (fun p Q' hQ' => Work.KeyLemma.BaseChange.placeOfPoint_baseChange_unique C L p Q' hQ')
    (fun p => Work.KeyLemma.BaseChange.ramIdx_placeOfPoint_baseChange C L p)

/-- **`Σ f` commutes with base change of the base field**, in the form of a statement about
divisors: the sum of the images of the points of the base-changed divisor `divMap C L D` in the
base-changed abelian variety `A_L` is the base change of the sum over `D`. -/
theorem sumMapOfModel_baseChange (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [IsProper A.hom] [IsCommMonObj A] (f : C.toOver ⟶ A) (D : C.Div) (hD : HasModel C D) :
    sumMapOfModel (Curve.baseChange C L) ((baseChangeFunctor k L).map f) (Curve.divMap C L D)
        ⟨SumDiv.baseChange C L (Classical.choose hD),
          (SumDiv.toDiv_baseChange (L := L) C (Classical.choose hD)).trans
            (by rw [sumMapOfModel_def C f hD])⟩ =
      Pt.baseChange L (sumMapOfModel C f D hD) := by
  haveI : IsProper ((baseChangeFunctor k L).obj A).hom := by
    change IsProper (pullback.snd A.hom (Work.CurveBasics.Curve.specMap k L))
    infer_instance
  have hbridge : SumDiv.toDiv (Curve.baseChange C L)
      (SumDiv.baseChange C L (Classical.choose hD)) = Curve.divMap C L D :=
    (SumDiv.toDiv_baseChange (L := L) C (Classical.choose hD)).trans (by rw [sumMapOfModel_def C f hD])
  have hchosen : Classical.choose
      (show HasModel (Curve.baseChange C L) (Curve.divMap C L D) from
        ⟨SumDiv.baseChange C L (Classical.choose hD), hbridge⟩) =
      SumDiv.baseChange C L (Classical.choose hD) :=
    Work.KeyLemma.Sum.toDiv_injective (Curve.baseChange C L)
      (by rw [sumMapOfModel_def (Curve.baseChange C L) ((baseChangeFunctor k L).map f) _, hbridge])
  unfold sumMapOfModel
  rw [hchosen, SumDiv.sumOfPoints_baseChange]

end

end Curve

end Work.KeyLemma
