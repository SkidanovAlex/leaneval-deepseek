import Mathlib.Data.Fintype.BigOperators
import Submission.Commons.Combinatorics.Ramsey.kvec_injective

namespace Commons.Combinatorics.Ramsey

/-- Membership in `varWord`: a word has a wildcard iff at least one of its letters is `none`. -/
lemma mem_varWord {k n : ℕ} {g : Fin n → Option (Fin k)} :
    g ∈ varWord k n ↔ ∃ i, g i = none := by simp [varWord]

/-- The words in `[k+1]^n` containing at least one wildcard: the complement of
`varWord k n` inside `Fin n → Option (Fin k)` is the image of `Fin n → Fin k`
under `some`. Hence the count `(k+1)^n - k^n`. -/
theorem card_varWord (k n : ℕ) : (varWord k n).card = (k+1)^n - k^n := by
  classical
  have hcompl : (varWord k n)ᶜ = Finset.univ.image (fun x : Fin n → Fin k =>
      (fun j => some (x j) : Fin n → Option (Fin k))) := by
    ext g
    simp only [Finset.mem_compl, mem_varWord, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hg' : ∀ j, ∃ a : Fin k, g j = some a := by
        intro j
        cases hh : g j with
        | none => exact absurd ⟨j, hh⟩ h
        | some a => exact ⟨a, rfl⟩
      choose x hx using hg'
      exact ⟨x, funext fun j => (hx j).symm⟩
    · rintro ⟨x, rfl⟩
      simp
  have hcard : ((varWord k n)ᶜ).card = k^n := by
    rw [hcompl, Finset.card_image_of_injective]
    · simp
    · intro x y h
      funext j
      exact Option.some.inj (congrFun h j)
  have h1 : (varWord k n).card + ((varWord k n)ᶜ).card = (k+1)^n := by
    rw [Finset.card_add_card_compl]
    simp [Fintype.card_option]
  omega

end Commons.Combinatorics.Ramsey