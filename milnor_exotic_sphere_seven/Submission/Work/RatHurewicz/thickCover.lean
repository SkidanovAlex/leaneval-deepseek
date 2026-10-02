import Mathlib
import Submission.Work.RatHurewicz.AttachPush.Defs
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.compressRel_cellU

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vocabulary for the "thickening + capped cap" cover of an attachment

For `Z = attachCells n Y ι f` (obtained from `Y` by attaching `(n+1)`-cells along maps out of
`cellSphere n`) and a radius `ρ`, this file introduces

* `cellBall ρ i` — the image of the closed model ball of radius `ρ` of the `i`-th cell,
* `thick ρ`     — the *thickening* `Z ∖ ⋃ᵢ cellBall ρ i` of the old part,
* `capCell β σ i` — the *capped* region of the `i`-th cell: the `br`-ball together with the part of
  the `sr`-ball below the "equator" `x_last < 0`,
* `cap β σ`     — the union of the `capCell`s.

The intended cover is `Z = cap β σ ∪ thick ρ` for `ρ < β < σ < 1`, and the point is that

* `capCell β σ i` is contractible (it is `ball(β) ∪ (lower half of ball(σ))`, a union of two
  contractible sets with contractible intersection),
* `capCell β σ i ∩ thick ρ` is contractible (the "C-shaped" region
  `(ρ < ‖·‖ < β) ∪ (ρ < ‖·‖ < σ, x_last < 0)`),
* `thick ρ` is a thickening of the old part, so `Work.RatHurewicz.thomCylAt_of_compress` applies.
-/

namespace Work.RatHurewicz

open scoped Topology unitInterval

noncomputable section

variable (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))

/-- The image of the closed model ball of radius `ρ` of the `i`-th attached cell. -/
def cellBall (ρ : ℝ) (i : ι) : Set (attachCells n Y ι f) :=
  cellMap n Y ι f i '' {y : cellDisk n | ‖(y : CellVec n)‖ ≤ ρ}

/-- The **thickening** of the old part: the complement of the union of the closed `ρ`-balls. -/
def thick (ρ : ℝ) : Set (attachCells n Y ι f) := Work.Serre.cellU f ρ

/-- The thickening is the complement of the union of the closed `ρ`-balls. -/
theorem thick_eq_compl (ρ : ℝ) : thick n Y ι f ρ = (⋃ i, cellBall n Y ι f ρ i)ᶜ := by
  simp only [thick, Work.Serre.cellU, Work.Serre.cellBallImg, Work.Serre.cellImg,
    Work.Serre.cellBallSet, cellBall, Set.compl_iUnion]

/-- The **capped region** of the `i`-th cell: the `br`-ball together with the part of the `sr`-ball
below the equator `x_last < 0`. -/
def capCell (br sr : ℝ) (i : ι) : Set (attachCells n Y ι f) :=
  cellMap n Y ι f i ''
    {y : cellDisk n | ‖(y : CellVec n)‖ < br ∨
      (‖(y : CellVec n)‖ < sr ∧ (y : CellVec n) (Fin.last (n+1)) < 0)}

/-- The union of the capped regions of all cells. -/
def cap (br sr : ℝ) : Set (attachCells n Y ι f) := ⋃ i, capCell n Y ι f br sr i

/-!
## Status (for the next session)
* `thick ρ = Work.Serre.cellU f ρ` and `Work.Serre.CellStep.compressRel_cellU` (proved) says the
  pair `(thick ρ, thick ρ ∩ range attachIncl)` is compressible in every dimension.
* Together with the **proved, axiom-clean** `Work.RatHurewicz.thomCylAt_of_compress`
  (`Submission/Work/RatHurewicz/thomCylAt_of_compress.lean`) this gives: `IH` over the old part
  implies `Work.Serre.ThomCylAt r N (restrictFibre q (thick ρ))` for every `0 < ρ < 1`.
* What is *not* yet available is an open set `C` covering the ρ-balls with `C ∩ thick ρ`
  contractible: the naive candidate `capCell br sr i` fails, because it contains the whole ball of
  radius `br`, so the overlap contains the full shell `{ρ < ‖·‖ < br} ≃ S^{n+1}`, whose inclusion is
  detected by the radial projection (degree 1).  A correct `C` must *cut* that shell; see the plan
  in `Submission/Work/RatHurewicz/gysinRangeFree.lean`.
-/
/-! ### The cut pieces (the corrected cover of the cell centres)
`capCell` above is **not** usable as the cover piece containing the cell centre: it contains the
whole `br`-ball, so its intersection with `thick ρ` contains the *full* shell
`{ρ < ‖·‖ < br} ≃ S^{n+1}`, whose inclusion of a sphere `S_a` is detected by the radial projection
`x ↦ x/‖x‖` (degree 1) — hence the intersection is not contractible.
The fix is to cut by a **cone** rather than by a half-space, and to truncate the cone at radius `ρ`
so that the whole ρ-sphere stays covered (the slit is `ρ < ‖y‖`, strictly, so the ρ-sphere is never slitted away), and `0 < ε < 1` (otherwise the cone is empty).  Write `s y` for the last coordinate of `y`.  The two
pieces are
* `coneDown ε sr i` — the *lower cone ball* `{‖y‖ < sr, s y + ε‖y‖ < 0}` (open, contractible: it is
  the cone over a cap of the sphere, times an interval);
* `ballSlit ρ sr ε i` — the sr-ball *slitted by the closed truncated cone*
  `{y : ρ < ‖y‖ ∧ s y + ε‖y‖ ≤ 0}` (open, contractible).
Their union is the whole sr-ball (a point with `‖y‖ ≥ ρ` on the cone boundary
`s y + ε‖y‖ = 0` lies in `coneDown` because the inequality there is strict), and the three pieces
`coneDown ε sr i`, `ballSlit ρ sr ε i`, `thick ρ` cover `Z`.  The point of the cone is that
  `ballSlit ρ sr ε i ∩ thick ρ = {ρ < ‖y‖ < sr, s y + ε‖y‖ > 0} ≃ (S^{n+1} ∖ cap) × (ρ,sr)`
is a *slitted* shell, hence contractible — unlike the full shell of `capCell`.
-/
/-- The last coordinate of a model cell vector, used for the cone cut. -/
noncomputable def cellLast {n : ℕ} (y : CellVec n) : ℝ := y (Fin.last (n+1))
/-- The **lower cone ball** of the `i`-th cell: the points of the sr-ball strictly below the cone
`s y + ε‖y‖ = 0`. -/
noncomputable def coneDown (ε sr : ℝ) (i : ι) : Set (attachCells n Y ι f) :=
  cellMap n Y ι f i ''
    {y : cellDisk n | ‖(y : CellVec n)‖ < sr ∧ cellLast (y : CellVec n)
      + ε * ‖(y : CellVec n)‖ < 0}
/-- The sr-ball of the `i`-th cell **slitted by the closed truncated cone**
`{y : ρ < ‖y‖ ∧ s y + ε‖y‖ ≤ 0}`. -/
noncomputable def ballSlit (ρ sr η : ℝ) (i : ι) : Set (attachCells n Y ι f) :=
  cellMap n Y ι f i ''
    {y : cellDisk n | ‖(y : CellVec n)‖ < sr ∧ ¬ (ρ ≤ ‖(y : CellVec n)‖ ∧
      cellLast (y : CellVec n) + η * ‖(y : CellVec n)‖ ≤ 0)}
/-! The statement `Work.RatHurewicz.cutCover` is proved in `Submission/Work/RatHurewicz/cutCoverProof.lean`
(it needs the piece lemmas of `cutCoverPiece.lean` etc., which import this file's vocabulary). -/

end


end Work.RatHurewicz
