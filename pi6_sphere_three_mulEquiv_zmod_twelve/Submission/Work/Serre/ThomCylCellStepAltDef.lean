import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cellular step of the CW-model Thom case, as a predicate (leaf module)

`Work.Serre.ThomCylCellStepAlt` is the single open node of the E3(b) tower.  It is declared here,
in a *leaf* module depending only on the vocabulary of the statement
(`Work.Serre.ThomCylDefs` + `Work.RatHurewicz.AttachCells`), because it is needed both

* downstream in `Submission/Work/Serre/eulerFibreRange.lean` (which turns it into `CWModelThomCase`
  and hence into `Work.Serre.EulerFibreRange`), and
* in this area's own proof of the cellular step
  (`Submission/Work/RatHurewicz/cellStepShell.lean`, `thomCylCellStepAlt_free`).

Importing `eulerFibreRange` from `cellStepShell.lean` is impossible: `Serre/cwModelThomCase.lean`
imports `RatHurewicz/cellStepShell`, so the edge would close a cycle
(`eulerFibreRange → cwModelThomCase → cellStepShell → eulerFibreRange`).  The declaration is
therefore moved here, unchanged (no statement was modified).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **The cellular step, as a predicate** (the statement of `Work.Serre.thomCylCellStepAlt`). -/
def ThomCylCellStepAlt : Prop :=
  ∀ (r N : ℕ) (hr : 1 ≤ r) (D : ℕ) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)),
    Work.StemsB.IsSerreFibration q →
    (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t)) →
    (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ)) →
    (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ)) →
    ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) →
    ThomCylAt r N q

end

end Work.Serre
