import Mathlib
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesDesign
namespace Work.WilG0

theorem projLastIter_eq (n m : ℕ) (X : Set (Fin (n + m) → ℝ)) :
    projLastIter n m X = {x : Fin n → ℝ | ∃ w : Fin m → ℝ, snocIt n m x w ∈ X} := by
  have key : ∀ m : ℕ, ∀ X : Set (Fin (n + m) → ℝ),
      projLastIter n m X = {x : Fin n → ℝ | ∃ w : Fin m → ℝ, snocIt n m x w ∈ X} := by
    intro m
    induction m with
    | zero =>
      intro X
      ext x
      simp only [projLastIter, snocIt, Set.mem_ofPred_eq]
      constructor
      · intro hx; exact ⟨Fin.elim0, hx⟩
      · rintro ⟨w, hx⟩; exact hx
    | succ m ih =>
      intro X
      ext x
      rw [projLastIter, ih (projLast X)]
      simp only [Set.mem_ofPred_eq, projLast, snocIt]
      constructor
      · rintro ⟨w, t, ht⟩
        exact ⟨Fin.snoc w t, by simpa only [Fin.init_snoc, Fin.snoc_last] using ht⟩
      · rintro ⟨w', hw'⟩
        exact ⟨Fin.init w', w' (Fin.last m), hw'⟩
  exact key m X

end Work.WilG0
