import Mathlib
import Submission.Work.TMC14Core.InvSumAux

/-!
# `TMC14Core.wordSum_self`

The weighted word sum `wordSum ω n a` (words of length `n` over `{U, V}` with
exactly `a` letters `U`, weighted by `ω ^ (invCount n f)`) at `a = n`: the count
condition forces every letter to be `U`, there is exactly one such word, and its
inversion number vanishes.  Hence `wordSum ω n n = 1`.
-/

noncomputable section

namespace Work.TMC14Core

/-- The constant word `U = (true,true)` of length `n`. -/
def allU (n : ℕ) : Fin n → Bool × Bool := fun _ => (true, true)

/-- The constant `U`-word has no `U`-before-`V` pairs, so inversion number `0`. -/
theorem invCount_allU (n : ℕ) : invCount n (allU n) = 0 := by
  simp [invCount, allU]

/-- The word inventory of `wordSum`: the constant `U`-word is the only word of
length `n` in `{U, V}^n` with exactly `n` letters `U`. -/
theorem wordSum_index_self (n : ℕ) :
    (Finset.univ.filter (fun f : Fin n → Bool × Bool =>
      (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
      (Finset.univ.filter (fun i => f i = (true, true))).card = n)) = {allU n} := by
  refine Finset.ext (fun f => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hcard⟩
    funext i
    have hsub : (Finset.univ.filter (fun i => f i = (true, true))) ⊆
        (Finset.univ : Finset (Fin n)) := Finset.filter_subset _ _
    have hcard' : (Finset.univ : Finset (Fin n)).card ≤
        (Finset.univ.filter (fun i => f i = (true, true))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact le_of_eq hcard.symm
    have heq := Finset.eq_of_subset_of_card_le hsub hcard'
    have hmem : i ∈ (Finset.univ.filter (fun i => f i = (true, true))) := by
      rw [heq]; exact Finset.mem_univ i
    simpa [allU] using (Finset.mem_filter.mp hmem).2
  · rintro rfl
    constructor
    · intro i; left; rfl
    · simp [allU]

theorem wordSum_self (ω : ℂ) (n : ℕ) : wordSum ω n n = 1 := by
  rw [wordSum, wordSum_index_self]
  simp [invCount_allU]

end Work.TMC14Core
