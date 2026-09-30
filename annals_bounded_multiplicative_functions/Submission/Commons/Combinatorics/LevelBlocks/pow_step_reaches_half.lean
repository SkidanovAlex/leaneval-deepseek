import Mathlib
import Submission.Commons.Analysis.ExpLog.exists_two_rpow_one_add_inv_ge_half

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Combinatorics.LevelBlocks

/-- Iterating the map `x ↦ x ^ (1 + 1/l)` (started from `2`) grows fast enough that,
unless at some step the sequence is already at least half of `m`, it reaches `m / 2`
within `2 + 2*l*(log(log m + 2) + 1)` steps.

Concretely: if `n` starts at least at `2` and at every step where `n j < m` either
`m ≤ 2 n (j+1)` or `(n j)^(1 + 1/l) ≤ n (j+1)`, then there is a `K` with
`K ≤ 2 + 2*l*(log(log m + 2) + 1)` and `m ≤ 2 n K`. -/
theorem pow_step_reaches_half {l : ℕ} (hl : 1 ≤ l) {m : ℕ} (hm : 4 ≤ m) {n : ℕ → ℕ}
    (h0 : 2 ≤ n 0)
    (hstep : ∀ j : ℕ, n j < m →
      m ≤ 2 * n (j + 1) ∨ (n j : ℝ) ^ (1 + 1 / (l : ℝ)) ≤ (n (j + 1) : ℝ)) :
    ∃ K : ℕ, (K : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) ∧
      m ≤ 2 * n K := by
  obtain ⟨B, hBle, hBge⟩ :=
    Commons.Analysis.ExpLog.exists_two_rpow_one_add_inv_ge_half l m hl hm
  by_contra hcon
  -- Under the contrary assumption every index up to `B` keeps `2 * n · < m`.
  have hcon' : ∀ K, K ≤ B → 2 * n K < m := by
    intro K hK
    have hKV : (K : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) :=
      le_trans (by exact_mod_cast hK) hBle
    exact not_le.mp (fun hle => hcon ⟨K, hKV, hle⟩)
  have hrpos : (0 : ℝ) < 1 + 1 / (l : ℝ) := by
    have hl0 : (0 : ℝ) < (l : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hl)
    positivity
  -- Induction: as long as we have not escaped, `n b` dominates `2 ^ ((1+1/l)^b)`.
  have key : ∀ b, b ≤ B → (2 : ℝ) ^ ((1 + 1 / (l : ℝ)) ^ b) ≤ (n b : ℝ) := by
    intro b
    induction b with
    | zero =>
      intro _
      simp only [pow_zero, Real.rpow_one]
      exact_mod_cast h0
    | succ b ih =>
      intro hb1
      have hb : b ≤ B := by omega
      have ihb := ih hb
      have hb1_lt : 2 * n (b + 1) < m := hcon' (b + 1) hb1
      have hnb : n b < m := by have := hcon' b hb; omega
      rcases hstep b hnb with h | h
      · omega
      · calc (2 : ℝ) ^ ((1 + 1 / (l : ℝ)) ^ (b + 1))
            = (2 : ℝ) ^ ((1 + 1 / (l : ℝ)) ^ b * (1 + 1 / (l : ℝ))) := by rw [pow_succ]
          _ = ((2 : ℝ) ^ ((1 + 1 / (l : ℝ)) ^ b)) ^ (1 + 1 / (l : ℝ)) := by
                rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          _ ≤ (n b : ℝ) ^ (1 + 1 / (l : ℝ)) :=
                Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ihb
                  (le_of_lt hrpos)
          _ ≤ (n (b + 1) : ℝ) := h
  have hBkey := key B le_rfl
  have hnB : 2 * n B < m := hcon' B le_rfl
  have hlt : (2 : ℝ) ^ ((1 + 1 / (l : ℝ)) ^ B) < (m : ℝ) / 2 := by
    have hnBr : (n B : ℝ) < (m : ℝ) / 2 := by
      have h2 : (2 : ℝ) * (n B : ℝ) < (m : ℝ) := by exact_mod_cast hnB
      linarith
    linarith [hBkey, hnBr]
  linarith [hBge, hlt]

end Commons.Combinatorics.LevelBlocks
