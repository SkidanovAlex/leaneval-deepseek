import Mathlib
import Submission.Work.Serre.serreC0Defs

/-!
# The cover of a cell attachment

Area **SERRE**: point-set geometry of the open cover used to compute the homology of a space
obtained by attaching cells (`Work.Serre.serreC0Range`).

For `X = Work.RatHurewicz.attachCells n Y ι f` (`Y` with `(n+2)`-cells glued on along
`f : ι → C(S^{n+1}, Y)`) we use the cover

* `coverOut` — `Y` together with the *outer* part `1/2 < ‖x‖` of every cell; this is open, and the
  radial push deforms it onto `Y` (staying inside `coverOut`), so `H_k(coverOut) ≅ H_k(Y)`;
* `coverIn` — the *inner* part `‖x‖ < 3/4` of every cell; a disjoint union of open balls, hence
  `H_k(coverIn) = 0` for `k ≥ 1`.

Their intersection is the disjoint union of the annuli `1/2 < ‖x‖ < 3/4`, homotopy equivalent (by
the radial map) to a disjoint union of spheres `S^{n+1}`, and the inclusion of the annulus into
`coverOut` is, up to this homotopy, the composite of the attaching map `f i` with the inclusion
`Y ↪ coverOut` — this is what identifies the kernel of `H_{n+1}(Y) → H_{n+1}(X)`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere n, Y)}

/-- The *outer* part of the model cell: the points of norm `> 1/2` (including the boundary). -/
def cellOuterSet (n : ℕ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | (1 / 2 : ℝ) < ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖}

/-- The *inner* part of the model cell: the points of norm `< 3/4`. -/
def cellInnerSet (n : ℕ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ < 3 / 4}

/-- The annular part of the model cell: `1/2 < ‖x‖ < 3/4`. -/
def cellRingSet (n : ℕ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | (1 / 2 : ℝ) < ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ ∧
    ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ < 3 / 4}

/-- The middle sphere of the annulus: the points of norm `5/8`. -/
def cellMidSet (n : ℕ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ = 5 / 8}

theorem isOpen_cellOuterSet (n : ℕ) : IsOpen (cellOuterSet n) := by
  have h : cellOuterSet n = (fun x : Work.RatHurewicz.cellDisk n =>
      ((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)) ⁻¹'
      {v : Work.RatHurewicz.CellVec n | (1 / 2 : ℝ) < ‖v‖} := rfl
  rw [h]
  exact (isOpen_lt continuous_const continuous_norm).preimage continuous_subtype_val

theorem isOpen_cellInnerSet (n : ℕ) : IsOpen (cellInnerSet n) := by
  have h : cellInnerSet n = (fun x : Work.RatHurewicz.cellDisk n =>
      ((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)) ⁻¹'
      {v : Work.RatHurewicz.CellVec n | ‖v‖ < 3 / 4} := rfl
  rw [h]
  exact (isOpen_lt continuous_norm continuous_const).preimage continuous_subtype_val

theorem cellInnerSet_subset_cellInner (n : ℕ) : cellInnerSet n ⊆ Work.RatHurewicz.cellInner n := by
  intro x hx
  have hx3 : ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ < 3 / 4 := hx
  have hx1 : ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp x.2
    simpa [dist_eq_norm] using h
  exact lt_of_lt_of_le hx3 (by norm_num)

theorem cellRingSet_subset_cellInner (n : ℕ) : cellRingSet n ⊆ Work.RatHurewicz.cellInner n :=
  fun x hx => cellInnerSet_subset_cellInner n hx.2

/-- The two sets `coverOut` and `coverIn` of the model cell. -/
def coverOutSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Y ⊕ (Σ _ : ι, Work.RatHurewicz.cellDisk n)) :=
  {a | (∃ y : Y, a = Sum.inl y) ∨
    ∃ (i : ι) (x : Work.RatHurewicz.cellDisk n),
      (1 / 2 : ℝ) < ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ ∧
        a = Sum.inr ⟨i, x⟩}

def coverInSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Y ⊕ (Σ _ : ι, Work.RatHurewicz.cellDisk n)) :=
  {a | ∃ (i : ι) (x : Work.RatHurewicz.cellDisk n),
    ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ < 3 / 4 ∧
      a = Sum.inr ⟨i, x⟩}

/-- The open cover member "outer part". -/
def coverOut (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  (Quotient.mk' (s := Relation.EqvGen.setoid (Work.RatHurewicz.attachRel n Y ι f))) ''
    (coverOutSet n Y ι f)

/-- The open cover member "inner part". -/
def coverIn (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  (Quotient.mk' (s := Relation.EqvGen.setoid (Work.RatHurewicz.attachRel n Y ι f))) ''
    (coverInSet n Y ι f)

end

end Work.Serre
