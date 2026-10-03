import Mathlib

namespace Work.KMTPlan.A6

/-- Elementary exponential-vs-quadratic arithmetic: for `q ≥ 8`, `2*q + 1 ≤ 2^(q-1)`.
(The induction step uses `2*(q+1)+1 ≤ 2*(2*q+1)` and the doubling `2^(q-1) + 2^(q-1) = 2^q`.) -/
private lemma two_mul_add_one_le_two_pow (q : ℕ) (hq : 8 ≤ q) : 2 * q + 1 ≤ 2 ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [Nat.add_sub_cancel]
    calc 2 * (q + 1) + 1 ≤ 2 * (2 * q + 1) := by omega
      _ ≤ 2 * 2 ^ (q - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ q := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]

/-- Elementary exponential-vs-quadratic arithmetic: for `q ≥ 8`, `q^2 + 2 ≤ 2^(q-1)`. -/
private lemma sq_add_two_le_two_pow (q : ℕ) (hq : 8 ≤ q) : q ^ 2 + 2 ≤ 2 ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [Nat.add_sub_cancel]
    have hA : 2 * q + 1 ≤ 2 ^ (q - 1) := two_mul_add_one_le_two_pow q hq
    have key : (q + 1) ^ 2 + 2 = (q ^ 2 + 2) + (2 * q + 1) := by ring
    rw [key]
    calc (q ^ 2 + 2) + (2 * q + 1) ≤ 2 ^ (q - 1) + 2 ^ (q - 1) := Nat.add_le_add ih hA
      _ = 2 ^ q := by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]

/-- In the "main regime" `q ≥ 8`, `k ≤ C₀ * q` with `C₀ ≤ q`, and `y ≤ 2^{q/2}` is comfortably
below the exponential scale `2^q`: indeed `k ≤ q^2`, `2y ≤ 2^q/4`, and `q^2 + 2 ≤ 2^{q-1}`,
so that `k + 2y ≤ q^2 + 2^q/4 ≤ (2^{q-1} - 2) + 2^q/4 ≤ 2^q - 2`. -/
theorem mainRegimeArith (C₀ q k : ℕ) (y : ℝ) (hC₀ : 1 ≤ C₀) (hCq : C₀ ≤ q) (hq : 8 ≤ q)
    (hk : k ≤ C₀ * q) (hy : y ≤ (2 : ℝ) ^ ((q : ℝ) / 2)) :
    (k : ℝ) + 2 * y ≤ (2 : ℝ) ^ q - 2 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  set x : ℝ := (2 : ℝ) ^ q with hxdef
  -- `k ≤ C₀ * q ≤ q * q = q^2`
  have hkq : k ≤ q * q := le_trans hk (Nat.mul_le_mul_right q hCq)
  have hkR : (k : ℝ) ≤ (q : ℝ) ^ 2 := by
    have h : (k : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hkq
    push_cast at h
    linarith
  -- `2^{q/2} ≤ 2^{q-3} = 2^q / 8 ≤ 2^q / 4`
  have hq3 : (q : ℝ) / 2 ≤ (q : ℝ) - 3 := by
    have : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hrpow : (2 : ℝ) ^ ((q : ℝ) / 2) ≤ x / 8 := by
    have hmono : (2 : ℝ) ^ ((q : ℝ) / 2) ≤ (2 : ℝ) ^ ((q : ℝ) - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq3
    have hsub : (2 : ℝ) ^ ((q : ℝ) - 3) = x / 8 := by
      rw [Real.rpow_sub h2pos, Real.rpow_natCast]
      rw [hxdef]
      norm_num
    linarith
  have hy2 : 2 * y ≤ x / 4 := by
    have h2 : 2 * y ≤ 2 * (2 : ℝ) ^ ((q : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  -- `q^2 + 2 ≤ 2^{q-1} = 2^q / 2`
  have hquad : (q : ℝ) ^ 2 + 2 ≤ x / 2 := by
    have h1 : q ^ 2 + 2 ≤ 2 ^ (q - 1) := sq_add_two_le_two_pow q hq
    have h2 : ((q ^ 2 + 2 : ℕ) : ℝ) ≤ ((2 ^ (q - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have hmul : 2 * (2 : ℝ) ^ (q - 1) = x := by
      rw [hxdef, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]
    have h3 : (2 : ℝ) ^ (q - 1) = x / 2 := by linarith
    linarith
  have hxnn : 0 ≤ x := by rw [hxdef]; positivity
  linarith

end Work.KMTPlan.A6
