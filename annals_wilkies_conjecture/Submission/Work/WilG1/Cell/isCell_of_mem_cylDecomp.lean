import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Cell

theorem isCell_of_mem_cylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) {κ : Set (Fin n → ℝ)} (hκ : κ ∈ C) :
    WilkiesDesign.IsCell n κ := by
  cases n with
  | zero =>
      rw [WilkiesDesign.IsCylDecomp] at h
      rw [h, Finset.mem_singleton] at hκ
      subst hκ
      exact WilkiesDesign.IsCell.zero
  | succ m =>
      exact (h.1 κ hκ).1

end Work.WilG1.Cell
