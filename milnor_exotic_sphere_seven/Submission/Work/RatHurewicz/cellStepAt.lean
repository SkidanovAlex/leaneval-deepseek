import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cellular step at a fixed cell dimension

`Work.Serre.ThomCylCellStepAlt` (`Submission/Work/Serre/eulerFibreRange.lean`) is the statement
"for every `D ≥ 2`, attaching `(D-1)`-cells (i.e. using `cellDisk (D-2) ⊂ ℝ^D`) to a path connected
base, the conclusion `Work.Serre.ThomCylAt` holds over the attachment".

For the *strong induction on the cell dimension* that the Mayer–Vietoris route to the cellular step
requires (`Submission/Work/Serre/THOMCYL_GLUING_NOTES.md`, and the shell step
`Work.Serre.bijective_cup_shell_of_thomCylAt`), the statement has to be split by dimension: the
shell step at level `D` uses the statement at level `D - 1`.  This file provides the dimension-indexed
predicate `Work.RatHurewicz.CellStepAt D` and the (quantifier-reordering) equivalence with
`Work.Serre.ThomCylCellStepAlt`.
-/

namespace Work.RatHurewicz

/-- **The cellular step at cell dimension `D`.**  For a path connected base `Γ`, an attachment
`Γ' = attachCells (D-2) Γ ι f` of `D`-dimensional cells, a Serre fibration `q` over `Γ'` whose
fibres are path connected and rationally `S^r` through degree `N`, and the conclusion known over the
old part, the conclusion holds over `Γ'`. -/
def CellStepAt (D : ℕ) : Prop :=
  ∀ (r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) {Γ : Type} [TopologicalSpace Γ]
    (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)),
    Work.StemsB.IsSerreFibration q →
    (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t)) →
    (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ)) →
    (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ)) →
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) →
    Work.Serre.ThomCylAt r N q

/-! ## The sphere case

`Work.RatHurewicz.SphThom k r N` is the statement of `Work.Serre.SphereThom k r N`
(`Submission/Work/Serre/thomCylAt_sphereInCell.lean`), restated here so that the level-crossing
transport `SphThom k r N ⟸ CellStepAt (k+1)` (the cell step at level `k+1` specialised to
`Γ = PUnit`, `ι = PUnit`, `f = const` and transported along
`Work.Serre.attachCellsPUnitSphere (k-1)`) can be *stated and proved* without importing the
(mid-edit) Serre file that carries `SphereThom`.  The two predicates have the same statement, so
each is definitionally equal to the other and either can be used where the other is expected.
-/

/-- **The sphere case**: `Work.Serre.ThomCylAt` over a fibration whose base is the model sphere
`cellSphere k`, with the fibre data given at one point only. -/
def SphThom (k r N : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (p : C(X, Work.RatHurewicz.cellSphere k))
    (z₀ : Work.RatHurewicz.cellSphere k),
    Work.StemsB.IsSerreFibration p →
    PathConnectedSpace (Work.StemsB.fibre p z₀) →
    (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p z₀)) t)) →
    Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p z₀)) r ≅ ModuleCat.of ℚ ℚ) →
    Work.Serre.ThomCylAt r N p

end Work.RatHurewicz
