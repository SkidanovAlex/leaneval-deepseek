import Mathlib
import Submission.Work.HP.NA.Setup

/-!
# `N_{d,n} ≥ n + 1` for `1 ≤ d`

`NN d n` is the number of degree-`d` monomials in `n+1` variables, i.e. the cardinality of the
subtype `Mon d n` of degree-`d` exponent vectors.  For `1 ≤ d` we exhibit an injection

`Fin (n+1) → Mon d n`,  `i ↦ x_i^d`,

whose exponent vector is `d` at position `i` and `0` elsewhere.  These `n+1` vectors are pairwise
distinct (the nonzero position recovers `i`), so `N_{d,n} ≥ n+1`.
-/

open Finset

namespace Work.HP.NA

noncomputable section

/-- Exponent vector of the monomial `x_i^d`: `d` at position `i` and `0` elsewhere. -/
private def evec (d n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℕ := fun j => if j = i then d else 0

private lemma evec_le (d n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 1)) : evec d n i j ≤ d := by
  simp only [evec]; split <;> omega

private lemma evec_sum (d n : ℕ) (i : Fin (n + 1)) : ∑ j, evec d n i j = d := by
  simp only [evec]; rw [Fintype.sum_ite_eq']

/-- The monomial `x_i^d` as an element of `Mon d n`. -/
private def mk (d n : ℕ) (i : Fin (n + 1)) : Mon d n :=
  ⟨fun j => ⟨evec d n i j, Nat.lt_succ_of_le (evec_le d n i j)⟩, by simpa using evec_sum d n i⟩

/-- For `1 ≤ d`, the number `N_{d,n}` of degree-`d` monomials in `n+1` variables is at least
`n+1` (witnessed by `x_0^d, …, x_n^d`). -/
theorem succ_le_NN (d n : ℕ) (hd : 1 ≤ d) : n + 1 ≤ Work.HP.NN d n := by
  have hinj : Function.Injective (mk d n) := by
    intro i i' h
    have hv := congrArg (fun m : Mon d n => ((m.1 i : Fin (d + 1)) : ℕ)) h
    simp only [mk, evec] at hv
    by_cases hii : i = i'
    · exact hii
    · simp [hii] at hv
      omega
  have := Fintype.card_le_of_injective (mk d n) hinj
  simp only [Fintype.card_fin] at this
  simpa [Work.HP.NN] using this

end

end Work.HP.NA
