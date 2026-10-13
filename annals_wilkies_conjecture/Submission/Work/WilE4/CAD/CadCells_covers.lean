import Mathlib
import Submission.Work.WilE4.CAD.Decomp

namespace Work.WilE4.CAD

/-- The cells of the decomposition at level `n` cover all of `ℝ^n`.

We argue by induction on `n`.  At level `0` there is nothing to prove, `CadCells 0 H` is the
single cell `topCell 0` with set `Set.univ`.

At level `k+1`, let `z : Fin (k+1) → ℝ`.  Its initial segment `Fin.init z` lies in `ℝ^k`, so by the
induction hypothesis (applied to the projection data `projDataT k H`) it lies in some base cell
`C ∈ CadCells k (projDataT k H)`.  The sign vector `signVec H z` of `H` at `z` is realised over `C`
— the point `Fin.snoc (Fin.init z) (z (Fin.last k)) = z` witnesses it — so the cylinder
`cell C H (signVec H z)` is a member of `CadCells (k+1) H`, and `z` lies in it by
construction. -/
theorem CadCells_covers {n : ℕ} (H : List (MvPolynomial (Fin n) ℝ)) :
    ∀ z : Fin n → ℝ, ∃ C ∈ CAD.CadCells n H, z ∈ C.set := by
  induction n with
  | zero =>
    intro z
    exact ⟨topCell 0, by simp [CadCells], by rw [topCell_set]; exact Set.mem_univ z⟩
  | succ k ih =>
    intro z
    obtain ⟨C, hC, hz⟩ := ih (projDataT k H) (Fin.init z)
    have hreal : RealizedOn H C (signVec H z) :=
      ⟨Fin.init z, hz, z (Fin.last k), fun i => by
        rw [Fin.snoc_init_self z]
        rfl⟩
    refine ⟨cell C H (signVec H z), ?_, ?_⟩
    · rw [mem_CadCells_succ]
      exact ⟨C, hC, signVec H z, hreal, rfl⟩
    · rw [mem_cell_iff]
      exact ⟨hz, fun _ => rfl⟩

end Work.WilE4.CAD
