import Mathlib
import Submission.Work.TMC16Core.Assembly.S0

namespace Work.TMC16Core.Assembly

/-- **Arithmetic of the `s = 0` windows (AJ §9, Lemma 9.4(2)).**

Both windows `W1s0 a U` and `W2s0 a U H M` lie in a strip of diameter `≲ H` around
`a` (shifted by `M` for `W2s0`), with `|a| ≤ 2H` and `2U ≤ H`.  Hence the sum `i + k`
of any two sites of the union is congruent, modulo `M` (and modulo `2M`), to a small
integer: there are `t ∈ {0,1,2}` and `|j| ≤ 8H + 8` with
`(H - 2) + i + k = j + t·M`.  Concretely

* `i, k ∈ W1s0`         ⟹  `j = H - 2 + i + k`,        `t = 0`;
* one in `W1s0`, one in `W2s0`  ⟹  `j = H - 2 + i + k - M`, `t = 1`;
* `i, k ∈ W2s0`         ⟹  `j = H - 2 + i + k - 2M`,   `t = 2`.

(In all three cases `j` is bounded by `7H + 4` in absolute value; `M` cancels, so the
hypothesis `hM : M = m·H` is not needed for the argument.) -/
theorem s0qn_cluster {U H : ℕ} {a m M i k : ℤ}
    (hH2 : 2 ≤ H) (h2U : 2 * U ≤ H) (hM : M = m * (H : ℤ)) (ha : |a| ≤ 2 * (H : ℤ))
    (hi : i ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
        Work.TMC16Core.Assembly.W2s0 a U H M)
    (hk : k ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
        Work.TMC16Core.Assembly.W2s0 a U H M) :
    ∃ t j : ℤ, 0 ≤ t ∧ t ≤ 2 ∧ |j| ≤ 8 * (H : ℤ) + 8 ∧
      ((H : ℤ) - 2) + i + k = j + t * M := by
  simp only [Finset.mem_union, W1s0, W2s0, Finset.mem_Icc] at hi hk
  have hHZ : (0 : ℤ) ≤ (H : ℤ) := by exact_mod_cast Nat.zero_le H
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  have h2UZ : 2 * (U : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2U
  rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩
  · exact ⟨0, (H : ℤ) - 2 + i + k, by norm_num, by norm_num,
      by rw [abs_le]; constructor <;> omega, by ring⟩
  · exact ⟨1, (H : ℤ) - 2 + i + k - M, by norm_num, by norm_num,
      by rw [abs_le]; constructor <;> omega, by ring⟩
  · exact ⟨1, (H : ℤ) - 2 + i + k - M, by norm_num, by norm_num,
      by rw [abs_le]; constructor <;> omega, by ring⟩
  · exact ⟨2, (H : ℤ) - 2 + i + k - 2 * M, by norm_num, by norm_num,
      by rw [abs_le]; constructor <;> omega, by ring⟩

end Work.TMC16Core.Assembly
