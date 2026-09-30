import Mathlib
import Submission.Work.GenusZero.Basic
import Submission.Work.CurveFacts.ptBaseChange_prod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj CategoryTheory.Obj

namespace Work.CurveFacts

universe u v

/-- Base change of points of a group scheme along a field extension `F/k` commutes with finite
products of points: `ptBaseChange F A (∏ i, u i) = ∏ i, ptBaseChange F A (u i)`.

The index type `I` lives in a separate universe `v` from `k`/`F` (which live in `u`), so that the
statement can be instantiated at `I := Fin n` (a type in universe `0`) while `k` ranges over
`Type u`. -/
theorem ptBaseChange_prodV {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {A : Work.GenusZero.Sch k} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    {I : Type v} [Fintype I] (u : I → (Work.GCBasics.specOf k F ⟶ A)) :
    Work.GenusZero.ptBaseChange (k := k) F A (∏ i, u i) =
      ∏ i, Work.GenusZero.ptBaseChange (k := k) F A (u i) := by
  exact map_prod (ptBaseChangeMonoidHom (k := k) (F := F) A) u Finset.univ

end Work.CurveFacts
