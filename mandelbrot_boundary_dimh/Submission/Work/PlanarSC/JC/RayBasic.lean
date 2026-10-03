import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells

/-!
# Basic open-cell vocabulary for the odd-crossing argument

A ray issued from an interior point of `cellUnion A` in a direction `1 + εI` (`ε > 0`) crosses
the wall set `wallSet A` (the union of the unit grid segments separating a cell of `A` from a cell
outside `A`) an odd number of times.  The parity argument needs to know that, along the ray,
membership in `cellUnion A` is locally constant away from `wallSet A` and flips transversally at
every crossing of `wallSet A`.

This file collects the elementary cell vocabulary behind those two facts.
-/

namespace Work.PlanarSC.JC

open Set

/-- An open cell is contained in the corresponding closed cell. -/
lemma iCell_subset_cell (p : ℤ × ℤ) :
    Work.HornSC.CellBoundaryJordan.iCell p ⊆ Work.HornSC.cell p := by
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩

/-- A closed cell and an open cell can meet only when they carry the same index. -/
lemma eq_of_mem_iCell_of_mem_cell {p q : ℤ × ℤ} {z : ℂ}
    (hp : z ∈ Work.HornSC.CellBoundaryJordan.iCell p) (hq : z ∈ Work.HornSC.cell q) :
    q = p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨k1, k2, k3, k4⟩ := hq
  have e1 : q.1 = p.1 := by
    have hA : (q.1 : ℝ) < (p.1 : ℝ) + 1 := lt_of_le_of_lt k1 h2
    have hB : (p.1 : ℝ) < (q.1 : ℝ) + 1 := lt_of_lt_of_le h1 k2
    have hA' : q.1 < p.1 + 1 := by exact_mod_cast hA
    have hB' : p.1 < q.1 + 1 := by exact_mod_cast hB
    omega
  have e2 : q.2 = p.2 := by
    have hC : (q.2 : ℝ) < (p.2 : ℝ) + 1 := lt_of_le_of_lt k3 h4
    have hD : (p.2 : ℝ) < (q.2 : ℝ) + 1 := lt_of_lt_of_le h3 k4
    have hC' : q.2 < p.2 + 1 := by exact_mod_cast hC
    have hD' : p.2 < q.2 + 1 := by exact_mod_cast hD
    omega
  exact Prod.ext e1 e2

/-- A point of the open cell `iCell p` lies in `cellUnion A` exactly when `p ∈ A`. -/
lemma mem_iCell_cellUnion_iff {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ Work.HornSC.CellBoundaryJordan.iCell p) :
    (z ∈ Work.HornSC.cellUnion A ↔ p ∈ A) := by
  constructor
  · intro hzA
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.mp hzA
    have hqp : q = p := eq_of_mem_iCell_of_mem_cell hz hzq
    rwa [hqp] at hq
  · intro hp
    exact Set.mem_iUnion₂.mpr ⟨p, hp, iCell_subset_cell p hz⟩

end Work.PlanarSC.JC
