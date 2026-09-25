import Mathlib.Data.Rat.Lemmas

namespace Commons.NumberTheory.Nat

/-- A nonzero natural number that is the square of a rational number is a square. -/
theorem isSquare_of_rat_sq {n : ℕ} (hn : n ≠ 0) (h : ∃ q : ℚ, q ^ 2 = (n : ℚ)) : IsSquare n := by
  rcases h with ⟨q, hq⟩
  exact (Rat.isSquare_natCast_iff (n := n)).mp ⟨q, by simpa [pow_two] using hq.symm⟩

end Commons.NumberTheory.Nat
