import Mathlib
import Submission.Work.Higman.Q3.two_pow_add_eq_two_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- If `2^A + 2^B + 1 = 2^C + 2^n` with `A, B, C < n`, then forced by size: the left side is at
most `2^(n-1) + 2^(n-1) + 1 = 2^n + 1` while the right side is at least `1 + 2^n`.  Both sides
equal `2^n + 1`, giving `2^A + 2^B = 2^n` and `2^C = 1`.  From `2^C = 1` we get `C = 0`; from
`2^A + 2^B = 2^n` with `A, B ≤ n-1` a matching bound pins `2^A = 2^B = 2^(n-1)`, so
`A = B = n - 1`. -/
theorem two_pow_add_add_one_eq {n A B C : ℕ} (hn : 1 ≤ n) (hA : A < n) (hB : B < n) (hC : C < n)
    (h : 2 ^ A + 2 ^ B + 1 = 2 ^ C + 2 ^ n) :
    A = B ∧ C = 0 ∧ A + 1 = n := by
  have hpred : n - 1 + 1 = n := by omega
  have hpowA : 2 ^ A ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_pred_of_lt hA)
  have hpowB : 2 ^ B ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_pred_of_lt hB)
  have h2 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [← two_mul, ← pow_succ', hpred]
  have hCpos : 1 ≤ 2 ^ C := Nat.one_le_two_pow
  have hsum : 2 ^ A + 2 ^ B + 1 = 2 ^ n + 1 := by omega
  have hAB : 2 ^ A + 2 ^ B = 2 ^ n := by omega
  have hC1 : 2 ^ C = 1 := by omega
  have hC0 : C = 0 := by
    rcases Nat.eq_zero_or_pos C with hc | hc
    · exact hc
    · exact absurd hC1 (ne_of_gt (Nat.one_lt_pow (by omega) (by norm_num)))
  have hAeq : A = n - 1 := by
    have hle : 2 ^ A + 2 ^ (n - 1) ≤ 2 ^ n := by omega
    have hge : 2 ^ n ≤ 2 ^ A + 2 ^ (n - 1) := by omega
    have heq : 2 ^ A + 2 ^ (n - 1) = 2 ^ n := le_antisymm hle hge
    have : 2 ^ A = 2 ^ (n - 1) := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  have hBeq : B = n - 1 := by
    have hle : 2 ^ B + 2 ^ (n - 1) ≤ 2 ^ n := by omega
    have hge : 2 ^ n ≤ 2 ^ B + 2 ^ (n - 1) := by omega
    have heq : 2 ^ B + 2 ^ (n - 1) = 2 ^ n := le_antisymm hle hge
    have : 2 ^ B = 2 ^ (n - 1) := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  exact ⟨by omega, hC0, by omega⟩

end Work.Higman.Q3
