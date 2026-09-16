import Mathlib.RingTheory.Polynomial.Basic

namespace Commons.Combinatorics.Polynomial

theorem card_degreeLE (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Nat.card (Polynomial.degreeLE F (n : WithBot ℕ)) = (Nat.card F) ^ (n + 1) := by
  rw [← Polynomial.degreeLT_succ_eq_degreeLE (R := F) (n := n)]
  rw [Nat.card_congr (Polynomial.degreeLTEquiv F (n + 1)).toEquiv]
  rw [Nat.card_fun, Nat.card_fin]

end Commons.Combinatorics.Polynomial