import Submission.Commons.Combinatorics.Composition.avoid_dvd_card_rec
import Submission.Commons.Combinatorics.TupleCount.card_eq_composition

open scoped BigOperators

namespace Commons.Combinatorics.TupleCount

/-- Recursion for the number of admissible tuples of weight `w`, valid in the range
`q + 1 ≤ w ≤ 2q - 2`.  The admissible tuples are reindexed by `q`-avoiding compositions and the
recursion for those (splitting off the first block) is applied. -/
theorem tpW_rec_large (q w : ℕ) (hq : 2 ≤ q) (hw : q < w) (hw2 : w ≤ 2 * q - 2) :
    Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
        (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
        (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
        (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w}
      = ∑ i ∈ Finset.range q,
        Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
          (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
          (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
          (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w - (i + 1)} := by
  have hlt : w < 2 * q := by omega
  have h1 : q + 1 ≤ w := by omega
  calc
    Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
        (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
        (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
        (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w}
        = Nat.card {c : Composition w // ∀ b ∈ c.blocks, ¬ q ∣ b} :=
          card_eq_composition q w hlt
    _ = ∑ i : Fin q, Nat.card {c : Composition (w - (i + 1)) // ∀ b ∈ c.blocks, ¬ q ∣ b} :=
          Commons.Combinatorics.Composition.avoid_dvd_card_rec q w hq h1 hw2
    _ = ∑ i ∈ Finset.range q,
          Nat.card {c : Composition (w - (i + 1)) // ∀ b ∈ c.blocks, ¬ q ∣ b} := by
          rw [Finset.sum_range]
    _ = ∑ i ∈ Finset.range q,
        Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
          (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
          (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
          (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w - (i + 1)} := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact (card_eq_composition q (w - (i + 1)) (by omega)).symm

end Commons.Combinatorics.TupleCount
