import Mathlib
import Submission.Work.RatHurewicz.cubePinchDefs
import Submission.Work.RatHurewicz.PsiKillsAux

/-!
# The general cubical homotopy-addition statement (Hutchings `(2.2b)`)

`PinchAll` is the statement that for **every** `k` and every cube `g : I^{k+1} → X` that is `x₀` on
its `(k-1)`-skeleton (`InSkel k z` = two coordinates of `z` at `0` or `1`), the signed product of
the classes of its `2(k+1)` faces is `1`.

This is the general form of Hutchings' homotopy addition theorem.  Its `k = 2` case is *proved*
(`Submission/Work/Stems/Hur2b`, the T-net and its collar); the general case is the single gap in
the pinch `Work.RatHurewicz.glue_class_of_collapse`, as recorded in
`Submission/Work/RatHurewicz/GluingPinch/PINCH_NOTES.md` (SESSION 8): the pinch follows from
`PinchAll` together with the two cheap ingredients `glue_extends` and `faceCube_glue_eq_piece`
(both proved in `glue_class_of_collapse.lean`).

Why the statement is true: the boundary map `g|_{∂I^{k+1}}` is `x₀` on the skeleton, so it factors
through the quotient of `∂I^{k+1}` by its skeleton — the wedge of the `2(k+1)` face spheres — and
the class of a map on the boundary sphere is the signed sum of the classes of the faces ("homotopy
addition"); the boundary map also extends over the cube (by `g` itself), hence is freely
null-homotopic and therefore trivial (`genLoop_eq_one_of_free_homotopic_const`, Hutchings `2.2a`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

/-- **The general cubical homotopy-addition statement** (Hutchings `(2.2b)`, all `k`): a cube
`g : I^{k+1} → Y` that is `x₀` on its `(k-1)`-skeleton has face classes whose signed product is
`1`.  The signs `(-1)^i`, `-(-1)^i` are those of the cubical boundary operator. -/
def PinchAll : Prop :=
  ∀ (k : ℕ) [Nontrivial (Fin k)] (Y : Type) [TopologicalSpace Y] (y : Y)
    (g : C(Work.Stems.Cubical.IC (k + 1), Y))
    (h : ∀ z : Work.Stems.Cubical.IC (k + 1), InSkel k z → g z = y),
    (∏ i : Fin (k + 1),
      (cl k Y y (faceCube k g h i false)) ^ ((-1 : ℤ) ^ (i : ℕ)) *
      (cl k Y y (faceCube k g h i true)) ^ (-((-1 : ℤ) ^ (i : ℕ)))) = 1

end

end Work.RatHurewicz
