import Mathlib
import Submission.Work.WilG4a.Defs

namespace Work.WilG4a

/-- The one-variable slice `y ↦ Fin.snoc l y` is smooth: it is an affine map
`y ↦ fun i => if i = Fin.last p then y else l i`. -/
theorem contDiffAt_finSnoc (p : ℕ) (l : Fin p → ℝ) (x : ℝ) (k : ℕ) :
    ContDiffAt ℝ k (fun y : ℝ => (Fin.snoc l y : Fin (p + 1) → ℝ)) x := by
  rw [contDiffAt_pi]
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]
    exact contDiffAt_const
  · simp only [Fin.snoc_last]
    exact contDiffAt_id

theorem slice_contDiffAt (p : ℕ) (g : (Fin (p + 1) → ℝ) → ℝ) (k : ℕ)
    (l : Fin p → ℝ) (x : ℝ)
    (h : Fin.snoc l x ∈ interior {w : Fin (p + 1) → ℝ | ContDiffAt ℝ k g w}) :
    ContDiffAt ℝ k (fun y : ℝ => g (Fin.snoc l y)) x := by
  have hg : ContDiffAt ℝ k g (Fin.snoc l x) := interior_subset h
  have hφ : ContDiffAt ℝ k (fun y : ℝ => (Fin.snoc l y : Fin (p + 1) → ℝ)) x :=
    contDiffAt_finSnoc p l x k
  exact ContDiffAt.comp x hg hφ

end Work.WilG4a
