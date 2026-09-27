import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

/-- The open sup-norm cube `PL.openCube r ⊆ PL.E n` is open, for every `r : ℝ`. -/
theorem isOpen_openCube (n : ℕ) (r : ℝ) : IsOpen (PL.openCube (n := n) r) := by
  have h : PL.openCube (n := n) r = ⋂ i : Fin n, {x : PL.E n | |x i| < r} := by
    ext x; simp [PL.openCube]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)

set_option linter.unusedVariables false in
theorem cubeChart_isOpen_image_openCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsOpen (c.toFun '' PL.openCube (n := n) r) := by
  have hsub : PL.openCube (n := n) r ⊆ PL.openCube (n := n) 1 :=
    fun x hx i => lt_of_lt_of_le (hx i) hr1
  have hpre : IsOpen ((Subtype.val ⁻¹' PL.openCube (n := n) r) : Set ↥(PL.openCube (n := n) 1)) :=
    (isOpen_openCube n r).preimage continuous_subtype_val
  have heq : c.toFun '' PL.openCube (n := n) r
      = ((PL.openCube (n := n) 1).domRestrict c.toFun) '' (Subtype.val ⁻¹' PL.openCube (n := n) r) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [heq]
  exact c.emb.isOpenMap _ hpre

end Work.Cells.Connell
