import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Cell

theorem exists_mem_of_cylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) (z : Fin n → ℝ) : ∃ κ ∈ C, z ∈ κ := by
  -- `IsCylDecomp` unfolds by recursion on the dimension: in dimension `0` the family is
  -- the singleton `{univ}`, and in dimension `n+1` covering is exactly the third conjunct.
  cases n with
  | zero =>
      rw [WilkiesDesign.IsCylDecomp] at h
      exact ⟨Set.univ, by rw [h]; simp, trivial⟩
  | succ m => exact h.2.2.1 z

end Work.WilG1.Cell
