import Mathlib
import Submission.Work.WilG4a.Defs

namespace Work.WilG4a

theorem isCell_fiber (n : ℕ) {C : Set (Fin (n + 1) → ℝ)} (hC : WilkiesDesign.IsCell (n + 1) C) (l : Fin n → ℝ) : (∃ x : ℝ, {y : ℝ | Fin.snoc l y ∈ C} = {x}) ∨ (∃ a b : EReal, {y : ℝ | Fin.snoc l y ∈ C} = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b}) := by
  set F : Set ℝ := {y : ℝ | Fin.snoc l y ∈ C} with hF
  cases hC with
  | graph _ f _ =>
    have hkey : ∀ y ∈ F, y = f l := by
      intro y hy
      simp only [hF, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hy
      exact hy.2
    by_cases hne : F.Nonempty
    · left
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, ?_⟩
      ext y
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hy => by rw [hkey y hy, ← hkey x hx], fun hy => by subst hy; exact hx⟩
    · right
      refine ⟨(0 : EReal), ⊥, ?_⟩
      ext y
      exact ⟨fun hy => absurd ⟨y, hy⟩ hne, fun hy => absurd hy.2 not_lt_bot⟩
  | band _ a b _ _ _ =>
    have hkey : ∀ y ∈ F, a l < (y : EReal) ∧ (y : EReal) < b l := by
      intro y hy
      simp only [hF, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hy
      exact hy.2
    by_cases hne : F.Nonempty
    · right
      obtain ⟨y0, hy0⟩ := hne
      have hy0' := hy0
      simp only [hF, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hy0'
      refine ⟨a l, b l, ?_⟩
      ext y
      constructor
      · intro hy; exact hkey y hy
      · intro hy
        simp only [hF, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hy0'.1, hy⟩
    · right
      refine ⟨(0 : EReal), ⊥, ?_⟩
      ext y
      exact ⟨fun hy => absurd ⟨y, hy⟩ hne, fun hy => absurd hy.2 not_lt_bot⟩

end Work.WilG4a
