/-
  `Work.WilE7.CoreStep.Basic`: small structural lemmas the `CoreLT_succ` assembly consumes.

  * `SubPf_init`: `SubPf` is stable under dropping the last coordinate.  This is what makes the
    base family of the inner `CoreLT n K` call usable as the base family of the outer step: the
    cells of the inner decomposition are `SubPf (n+1)`, and their `Fin.init`-images must be
    `SubPf n` for the cell lemmas (`multiStrata_cellsX`, `sheets_of_localGraph`) to apply.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.GraphCellAux.subPf_projFirst

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep
open WilkiesDesign WilkiesDesign.E

/-- `projFirst n 1` is `Fin.init`. -/
theorem projFirst_one_eq_init {n : ℕ} (y : Fin (n + 1) → ℝ) :
    projFirst n 1 y = Fin.init y := by
  funext i
  exact congrArg y (Fin.ext rfl)

/-- **`SubPf` is stable under `Fin.init`.**  Dropping the last coordinate of a sub-Pfaffian set
of `ℝ^{n+1}` gives a sub-Pfaffian set of `ℝ^n`. -/
theorem SubPf_init {n : ℕ} {Y : Set (Fin (n + 1) → ℝ)} (h : WilkiesDesign.E.SubPf (n + 1) Y) :
    WilkiesDesign.E.SubPf n (Fin.init '' Y) := by
  have h' := Work.WilE7.GraphCellAux.subPf_projFirst (n := n) (M := 1) h
  have himg : projFirst n 1 '' Y = Fin.init '' Y := by
    rw [show projFirst n 1 = Fin.init from funext projFirst_one_eq_init]
  rwa [himg] at h'

end Work.WilE7.CoreStep
