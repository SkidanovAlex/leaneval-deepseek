import Mathlib
import Submission.Work.Higman.Q3.L12.three_pow_helpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Uniqueness of the representation `2 ^ u + 2 ^ v`

If `u ≤ v`, `d ≤ e` and `2 ^ u + 2 ^ v = 2 ^ d + 2 ^ e`, then `u = d` and `v = e`:
a number is the sum of at most two distinct powers of two in at most one way
(uniqueness of the binary expansion in the two-bit case).

The proof factors the exact power of two out of each side.  For `u ≤ v`,

`2 ^ u + 2 ^ v = 2 ^ u * (1 + 2 ^ (v - u))`,

where the cofactor `1 + 2 ^ (v - u)` is odd as soon as `u < v`; when `u = v` the whole
sum collapses to `2 ^ (u + 1) * 1` with odd cofactor `1`.  Cancelling the exact power of
two against odd cofactors (`pow_two_mul_eq`, from `three_pow_helpers`) pins down the
smaller exponent; the remaining equality of cofactors rules out the mixed cases and gives
the larger exponent as well.
-/

namespace Work.Higman.Q3.L12

theorem pair_unique_le {u v d e : ℕ} (huv : u ≤ v) (hde : d ≤ e)
    (h : 2 ^ u + 2 ^ v = 2 ^ d + 2 ^ e) : u = d ∧ v = e := by
  -- Factor out `2 ^ u` resp. `2 ^ d`.
  have hL : 2 ^ u + 2 ^ v = 2 ^ u * (1 + 2 ^ (v - u)) := by
    rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le huv]
  have hR : 2 ^ d + 2 ^ e = 2 ^ d * (1 + 2 ^ (e - d)) := by
    rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le hde]
  rcases eq_or_lt_of_le huv with rfl | huv'
  · -- `u = v`: the left hand side is `2 ^ (u + 1) * 1`.
    rcases eq_or_lt_of_le hde with rfl | hde'
    · -- `d = e`: compare the powers of two.
      have h1 : 2 ^ (u + 1) = 2 ^ (d + 1) := by
        rw [← two_pow_add_self u, ← two_pow_add_self d]
        exact h
      have hud : u = d := by
        have := Nat.pow_right_injective (le_refl 2) h1
        omega
      exact ⟨hud, hud⟩
    · -- `d < e`: the odd cofactor `1 + 2 ^ (e - d) > 1` cannot equal `1`.
      have ho2 : Odd (1 + 2 ^ (e - d)) := odd_one_add_two_pow (by omega)
      have heq : 2 ^ (u + 1) * 1 = 2 ^ d * (1 + 2 ^ (e - d)) := by
        rw [mul_one, ← two_pow_add_self u, ← hR]
        exact h
      obtain ⟨-, hf⟩ := pow_two_mul_eq odd_one ho2 heq
      have hz : 2 ^ (e - d) = 0 := by omega
      exact absurd hz (ne_of_gt (pow_pos (by norm_num : (0 : ℕ) < 2) _))
  · -- `u < v`: the left hand side is `2 ^ u * (1 + 2 ^ (v - u))` with odd cofactor.
    rcases eq_or_lt_of_le hde with rfl | hde'
    · -- `d = e`: the odd cofactor `1 + 2 ^ (v - u) > 1` cannot equal `1`.
      have ho1 : Odd (1 + 2 ^ (v - u)) := odd_one_add_two_pow (by omega)
      have heq : 2 ^ u * (1 + 2 ^ (v - u)) = 2 ^ (d + 1) * 1 := by
        rw [mul_one, ← two_pow_add_self d, ← hL]
        exact h
      obtain ⟨-, hf⟩ := pow_two_mul_eq ho1 odd_one heq
      have hz : 2 ^ (v - u) = 0 := by omega
      exact absurd hz (ne_of_gt (pow_pos (by norm_num : (0 : ℕ) < 2) _))
    · -- both sides have an odd cofactor `> 1`: match exponents, then cofactors.
      have ho1 : Odd (1 + 2 ^ (v - u)) := odd_one_add_two_pow (by omega)
      have ho2 : Odd (1 + 2 ^ (e - d)) := odd_one_add_two_pow (by omega)
      have heq : 2 ^ u * (1 + 2 ^ (v - u)) = 2 ^ d * (1 + 2 ^ (e - d)) := by
        rw [← hL, ← hR]
        exact h
      obtain ⟨hud, hf⟩ := pow_two_mul_eq ho1 ho2 heq
      have hvu : v - u = e - d :=
        Nat.pow_right_injective (le_refl 2) (Nat.add_left_cancel hf)
      exact ⟨hud, by omega⟩

end Work.Higman.Q3.L12
