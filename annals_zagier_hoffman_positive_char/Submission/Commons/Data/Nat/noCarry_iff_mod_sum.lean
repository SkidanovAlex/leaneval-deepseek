import Mathlib

namespace Commons.Data.Nat

/-- Decomposition of `a` modulo `p ^ (k+1)` into its residue modulo `p ^ k` plus the
`k`-th base-`p` digit of `a` times `p ^ k`. -/
private theorem mod_pow_succ_eq (a p k : ℕ) (hp : 0 < p) :
    a % p ^ (k + 1) = a % p ^ k + p ^ k * (a / p ^ k % p) := by
  have hM : 0 < p ^ k := pow_pos hp k
  have hr : a % p ^ k < p ^ k := Nat.mod_lt _ hM
  have key : p ^ k * (a / p ^ k) =
      (a / p ^ k / p) * p ^ (k + 1) + (a / p ^ k % p) * p ^ k := by
    conv_lhs => rw [← Nat.div_add_mod (a / p ^ k) p]
    rw [pow_succ]
    ring
  have hdec : a = ((a / p ^ k % p) * p ^ k + a % p ^ k) + (a / p ^ k / p) * p ^ (k + 1) := by
    conv_lhs => rw [← Nat.div_add_mod a (p ^ k)]
    rw [key]
    ring
  have hp1 : a / p ^ k % p + 1 ≤ p := Nat.succ_le_of_lt (Nat.mod_lt _ hp)
  have hS : (a / p ^ k % p) * p ^ k + a % p ^ k < p ^ (k + 1) := by
    calc (a / p ^ k % p) * p ^ k + a % p ^ k
        < (a / p ^ k % p) * p ^ k + p ^ k := Nat.add_lt_add_left hr _
      _ = (a / p ^ k % p + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ hp1
      _ = p ^ (k + 1) := by rw [pow_succ, mul_comm]
  conv_lhs => rw [hdec]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hS]
  ring

/-- The `k`-th base-`p` digit of `a` times `p ^ k` is at most `a % p ^ (k+1)`. -/
private theorem digit_mul_le_mod_pow_succ (a p k : ℕ) (hp : 0 < p) :
    p ^ k * (a / p ^ k % p) ≤ a % p ^ (k + 1) := by
  rw [mod_pow_succ_eq a p k hp]
  exact Nat.le_add_left _ _

/-- No-carry in base-`p` addition: the digit-wise condition is equivalent to the
partial-sum condition. -/
theorem noCarry_iff_mod_sum {p a b : ℕ} (hp : 2 ≤ p) :
    (∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p) ↔
      ∀ k : ℕ, a % p ^ k + b % p ^ k < p ^ k := by
  have hp0 : 0 < p := by omega
  constructor
  · intro h k
    induction k with
    | zero => simp [Nat.mod_one]
    | succ k ih =>
      have hd : a / p ^ k % p + b / p ^ k % p < p := h k
      have hgoal : (a % p ^ k + p ^ k * (a / p ^ k % p)) +
            (b % p ^ k + p ^ k * (b / p ^ k % p))
          = (a % p ^ k + b % p ^ k) + p ^ k * (a / p ^ k % p + b / p ^ k % p) := by
        ring
      have hsd : a % p ^ k + b % p ^ k + 1 ≤ p ^ k := by omega
      have hd1 : a / p ^ k % p + b / p ^ k % p + 1 ≤ p := by omega
      have hmul : p ^ k * (a / p ^ k % p + b / p ^ k % p + 1) ≤ p ^ k * p :=
        Nat.mul_le_mul_left _ hd1
      have hkey : (a % p ^ k + b % p ^ k + p ^ k * (a / p ^ k % p + b / p ^ k % p)) + 1
          ≤ p ^ k * p := by
        calc (a % p ^ k + b % p ^ k + p ^ k * (a / p ^ k % p + b / p ^ k % p)) + 1
            = (a % p ^ k + b % p ^ k + 1) + p ^ k * (a / p ^ k % p + b / p ^ k % p) := by ring
          _ ≤ p ^ k + p ^ k * (a / p ^ k % p + b / p ^ k % p) := Nat.add_le_add_right hsd _
          _ = p ^ k * (a / p ^ k % p + b / p ^ k % p + 1) := by ring
          _ ≤ p ^ k * p := hmul
      have hlt : a % p ^ k + b % p ^ k + p ^ k * (a / p ^ k % p + b / p ^ k % p)
          < p ^ k * p := by omega
      rw [mod_pow_succ_eq a p k hp0, mod_pow_succ_eq b p k hp0, hgoal, pow_succ]
      exact hlt
  · intro h i
    have hle_a : p ^ i * (a / p ^ i % p) ≤ a % p ^ (i + 1) :=
      digit_mul_le_mod_pow_succ a p i hp0
    have hle_b : p ^ i * (b / p ^ i % p) ≤ b % p ^ (i + 1) :=
      digit_mul_le_mod_pow_succ b p i hp0
    have hgoal : p ^ i * (a / p ^ i % p + b / p ^ i % p) < p ^ i * p := by
      rw [Nat.mul_add]
      calc p ^ i * (a / p ^ i % p) + p ^ i * (b / p ^ i % p)
          ≤ a % p ^ (i + 1) + b % p ^ (i + 1) := Nat.add_le_add hle_a hle_b
        _ < p ^ (i + 1) := h (i + 1)
        _ = p ^ i * p := by rw [pow_succ]
    exact Nat.lt_of_mul_lt_mul_left hgoal

end Commons.Data.Nat
