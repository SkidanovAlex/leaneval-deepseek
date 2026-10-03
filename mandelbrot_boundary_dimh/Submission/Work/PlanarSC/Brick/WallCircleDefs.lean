import Mathlib
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs

/-!
# The centre of a unit lattice cell

Vocabulary for `Work.PlanarSC.Brick.exists_enclosing_wall_circle`: the centre `cellCenter p` of the
closed unit cell `cell p` (which lies in the interior of the cell).
-/

namespace Work.PlanarSC.Brick

open Set

/-- The centre of the unit cell at `p`. -/
noncomputable def cellCenter (p : ℤ × ℤ) : ℂ := ((p.1 : ℝ) + 1 / 2) + ((p.2 : ℝ) + 1 / 2) * Complex.I

@[simp] lemma cellCenter_re (p : ℤ × ℤ) : (cellCenter p).re = (p.1 : ℝ) + 1 / 2 := by
  simp [cellCenter]

@[simp] lemma cellCenter_im (p : ℤ × ℤ) : (cellCenter p).im = (p.2 : ℝ) + 1 / 2 := by
  simp [cellCenter]

lemma cellCenter_mem_cell (p : ℤ × ℤ) : cellCenter p ∈ Work.HornSC.cell p := by
  rw [Work.HornSC.mem_cell, cellCenter_re, cellCenter_im]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma cellCenter_mem_interior_cell (p : ℤ × ℤ) :
    cellCenter p ∈ interior (Work.HornSC.cell p) := by
  have hopen : IsOpen {z : ℂ | (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 1} := by
    have h1 : IsOpen {z : ℂ | (p.1 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z.re < (p.1 : ℝ) + 1} := isOpen_lt Complex.continuous_re continuous_const
    have h3 : IsOpen {z : ℂ | (p.2 : ℝ) < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have h4 : IsOpen {z : ℂ | z.im < (p.2 : ℝ) + 1} := isOpen_lt Complex.continuous_im continuous_const
    have h := ((h1.inter h2).inter (h3.inter h4))
    convert h using 1
    ext z; simp [and_assoc]
  refine interior_maximal ?_ hopen ?_
  · intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [Work.HornSC.mem_cell]
    exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩
  · rw [Set.mem_setOf_eq, cellCenter_re, cellCenter_im]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma cellCenter_mem_cellUnion {B : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ B) :
    cellCenter p ∈ Work.HornSC.cellUnion B :=
  Work.HornSC.cell_subset_cellUnion hp (cellCenter_mem_cell p)

lemma cellCenter_mem_interior_cellUnion {B : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ B) :
    cellCenter p ∈ interior (Work.HornSC.cellUnion B) := by
  refine interior_mono ?_ (cellCenter_mem_interior_cell p)
  intro z hz
  exact Work.HornSC.cell_subset_cellUnion hp hz

end Work.PlanarSC.Brick
