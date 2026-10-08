import Mathlib
import Submission.Work.ZassenhausSuzuki.pow_two_defs
import Submission.Work.ZassenhausSuzuki.r_eq_two_of_oddPart_bound
import Submission.Work.ZassenhausSuzuki.p_add_one_eq_pow_two_of_oddPart_bound
import Submission.Work.ZassenhausSuzuki.p_eq_three_of_p_add_one_pow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-power classification behind the Zassenhaus–Suzuki argument

If `p` is an odd prime, `r ≥ 2`, `2 ^ k` divides `p ^ r - 1` with
`2 * (p ^ r - 1) ≤ 2 ^ k * (p - 1)`, and `p` divides `2 ^ a + 1` for some `a`, then
`p = 3`, `r = 2` and `2 ^ k = 8`.

Writing `p ^ r - 1 = 2 ^ k * m`, the second hypothesis is exactly `2 * m ≤ p - 1`, and since
`oddPart (p ^ r - 1) ≤ m` we get the key bound `2 * oddPart (p ^ r - 1) ≤ p - 1`.  The three
imported arithmetic lemmas turn that bound into `r = 2`, then `p + 1 = 2 ^ j`, and finally
`p = 3` using the last hypothesis.
-/

namespace Work.ZassenhausSuzuki

theorem pow_two_classification {p r k a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hdvd : 2 ^ k ∣ p ^ r - 1) (hle : 2 * (p ^ r - 1) ≤ 2 ^ k * (p - 1))
    (ha : p ∣ 2 ^ a + 1) : p = 3 ∧ r = 2 ∧ 2 ^ k = 8 := by
  obtain ⟨m, hm⟩ := hdvd
  -- `2 ^ k * m = p ^ r - 1`, so the second hypothesis reads `2 * m ≤ p - 1`.
  have h2m : 2 * m ≤ p - 1 := by
    have h1 : 2 * (2 ^ k * m) ≤ 2 ^ k * (p - 1) := by rw [← hm]; exact hle
    have h2 : 2 ^ k * (2 * m) ≤ 2 ^ k * (p - 1) := by
      calc 2 ^ k * (2 * m) = 2 * (2 ^ k * m) := by ring
        _ ≤ 2 ^ k * (p - 1) := h1
    exact Nat.le_of_mul_le_mul_left h2 (pow_pos (by norm_num : (0 : ℕ) < 2) k)
  -- The odd part of `p ^ r - 1` is the odd part of `m`, hence `≤ m`.
  have hu_eq : oddPart (p ^ r - 1) = oddPart m := by
    rw [hm, oddPart_self_pow_mul]
  have hu_le : oddPart (p ^ r - 1) ≤ m := by
    rw [hu_eq]; exact oddPart_le m
  -- Key bound.
  have H : 2 * oddPart (p ^ r - 1) ≤ p - 1 :=
    le_trans (Nat.mul_le_mul_left 2 hu_le) h2m
  have hr2 : r = 2 := r_eq_two_of_oddPart_bound hp hp2 hr H
  have H2 : 2 * oddPart (p ^ 2 - 1) ≤ p - 1 := by
    rw [hr2] at H; exact H
  obtain ⟨j, hj⟩ := p_add_one_eq_pow_two_of_oddPart_bound hp hp2 H2
  have hp3 : p = 3 := p_eq_three_of_p_add_one_pow_two hp hp2 hj ha
  refine ⟨hp3, hr2, ?_⟩
  -- With `p = 3`, `r = 2` we have `2 ^ k * m = 8` and `2 * m ≤ 2`, so `m = 1`.
  have hm8 : 2 ^ k * m = 8 := by
    rw [← hm, hp3, hr2]
    norm_num
  have hm_le : m ≤ 1 := by omega
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm8; omega
    · exact h
  have hm1 : m = 1 := le_antisymm hm_le hm_pos
  simpa [hm1] using hm8

end Work.ZassenhausSuzuki
