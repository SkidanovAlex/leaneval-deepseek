import Mathlib
import Submission.Work.TMC14Core.InvSumAux

namespace Work.TMC14Core

/-- The words of length `n` over `{U, V}` (`U = (true,true)`, `V = (false,true)`)
having exactly `0` letters `U`: there is only the all-`V` word. -/
theorem filter_card_U_eq_zero (n : ℕ) :
    (Finset.univ.filter (fun f : Fin n → Bool × Bool =>
      (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
        (Finset.univ.filter (fun i => f i = (true, true))).card = 0))
      = {(fun _ : Fin n => (false, true))} := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hall, hcard⟩
    funext i
    have hemp : (Finset.univ.filter (fun i => f i = (true, true))) = ∅ :=
      Finset.card_eq_zero.mp hcard
    have hi : ¬ (f i = (true, true)) := by
      intro h
      have : i ∈ (Finset.univ.filter (fun i => f i = (true, true))) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
      rw [hemp] at this
      simp at this
    rcases hall i with h | h
    · exact absurd h hi
    · exact h
  · rintro rfl
    refine ⟨fun i => Or.inr rfl, ?_⟩
    simp

/-- The all-`V` word has no `U`-before-`V` inversion. -/
theorem invCount_allV (n : ℕ) :
    invCount n (fun _ : Fin n => (false, true)) = 0 := by
  rw [invCount]
  simp

theorem wordSum_zero (ω : ℂ) (n : ℕ) : wordSum ω n 0 = 1 := by
  rw [wordSum, filter_card_U_eq_zero n, Finset.sum_singleton, invCount_allV n, pow_zero]

end Work.TMC14Core
