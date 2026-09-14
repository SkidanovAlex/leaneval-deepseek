import Mathlib
import Submission.Commons.Data.Nat.card_squarefull_le

namespace Commons.NumberTheory.Nat

/-- The number of squarefull (powerful) integers `N` with `1 ≤ N ≤ Y` is `O(√Y)`.

We prove the explicit bound `≤ 4 * (√Y + 1)` by reducing to
`Commons.Data.Nat.card_squarefull_le`, which bounds the larger set of all squarefull
`N ≤ Y` by `4 * (Nat.sqrt Y + 1)`, and using `Nat.sqrt Y ≤ Real.sqrt Y`. -/
theorem ncard_squarefull_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ,
      ({N : ℕ | 1 ≤ N ∧ N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} : Set ℕ).ncard
        ≤ C * (Real.sqrt (Y : ℝ) + 1) := by
  refine ⟨4, by norm_num, fun Y => ?_⟩
  have hsub : ({N : ℕ | 1 ≤ N ∧ N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} : Set ℕ)
      ⊆ {N : ℕ | N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} :=
    fun _ hN => ⟨hN.2.1, hN.2.2⟩
  have hfin : ({N : ℕ | N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} : Set ℕ).Finite :=
    (Set.finite_Iic Y).subset fun _ hN => hN.1
  have hcard : ({N : ℕ | 1 ≤ N ∧ N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} : Set ℕ).ncard
      ≤ 4 * (Nat.sqrt Y + 1) :=
    le_trans (Set.ncard_le_ncard hsub hfin) (Commons.Data.Nat.card_squarefull_le Y)
  have hcast : ((4 * (Nat.sqrt Y + 1) : ℕ) : ℝ) ≤ 4 * (Real.sqrt (Y : ℝ) + 1) := by
    have hns : ((Nat.sqrt Y : ℕ) : ℝ) ≤ Real.sqrt Y := Real.nat_sqrt_le_real_sqrt
    push_cast
    nlinarith [hns]
  exact le_trans (by exact_mod_cast hcard) hcast

end Commons.NumberTheory.Nat
