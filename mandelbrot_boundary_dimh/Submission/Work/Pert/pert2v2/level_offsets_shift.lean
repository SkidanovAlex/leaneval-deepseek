import Mathlib
import Submission.Work.Pert.pert2v2.level_offsets

namespace Work.Pert.pert2v2

theorem level_offsets_shift {m₀ m n : ℕ} {k : ℕ → ℤ} (hm : 1 ≤ m)
    (hanti : ∀ j, j + 1 < m → k (j+1) ≤ k j)
    (hneg : ∀ j, 1 ≤ j → j ≤ m - 1 → k j ≤ 0)
    (hn : ((-k (m-1)).toNat : ℕ) ≤ n)
    (hnn : (m₀ : ℤ) ≤ k (m-1) + (n : ℤ))
    (hlvl : ∀ j, j + 1 < m → (m₀ : ℤ) ≤ k j - k (j+1)) :
    ∃ t : ℕ → ℕ, t 0 = 0 ∧ t m = n ∧ Monotone t ∧
      (∀ j, j + 1 < m → (t (j+1) : ℤ) = - k (j+1)) ∧
      (∀ j, j < m → (m₀ : ℤ) ≤ k j + (t (j+1) : ℤ)) := by
  -- The offsets `t` are forced: `t 0 = 0`, `t (j+1) = -k (j+1)` for `j+1 < m`, and only `t m = n`
  -- is free.  We take the canonical choice, with `t j = (-k j).toNat` for the forced indices and
  -- `t j = n` for `j ≥ m`.
  have hm0 : m ≠ 0 := by omega
  set t : ℕ → ℕ := fun j => if j = 0 then 0 else if j < m then (-k j).toNat else n with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have htm : t m = n := by simp [htdef, hm0]
  have htlt : ∀ j, j < m → j ≠ 0 → t j = (-k j).toNat := by
    intro j hjm hj0; simp [htdef, hj0, hjm]
  have htge : ∀ j, m ≤ j → t j = n := by
    intro j hj
    have hj0 : j ≠ 0 := by omega
    have hjm : ¬ j < m := by omega
    simp [htdef, hj0, hjm]
  have hneg' : ∀ j, j + 1 < m → k (j+1) ≤ 0 := by
    intro j hj; exact hneg (j+1) (by omega) (by omega)
  refine ⟨t, ht0, htm, ?_, ?_, ?_⟩
  · -- monotonicity: `t` increases because `k` is antitone and `n ≥ -k (m-1)`
    refine monotone_nat_of_le_succ (fun j => ?_)
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [ht0]; exact Nat.zero_le _
    · rcases lt_or_ge (j + 1) m with hjm | hjm
      · rw [htlt j (by omega) (by omega), htlt (j+1) hjm (by omega)]
        exact Int.toNat_le_toNat (by have := hanti j hjm; omega)
      · rcases eq_or_lt_of_le hjm with heq | hgt
        · rw [← heq, htm, htlt j (by omega) (by omega)]
          have hjl : j = m - 1 := by omega
          rw [hjl]; exact hn
        · rw [htge j (by omega), htge (j+1) (by omega)]
  · -- the forced value `t (j+1) = -k (j+1)`
    intro j hj
    rw [htlt (j+1) hj (by omega)]
    exact Int.toNat_of_nonneg (by have := hneg' j hj; omega)
  · -- the level condition
    intro j hj
    rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with hlt | heq
    · rw [htlt (j+1) hlt (by omega), Int.toNat_of_nonneg (by have := hneg' j hlt; omega)]
      have := hlvl j hlt
      linarith
    · rw [heq, htm]
      have hjl : j = m - 1 := by omega
      rw [hjl]; exact hnn

end Work.Pert.pert2v2
