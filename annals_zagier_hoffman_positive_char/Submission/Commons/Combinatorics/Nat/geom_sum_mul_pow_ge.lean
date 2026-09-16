import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Combinatorics.Nat

/-
Arithmetic core of the tail estimate in the `π̃`-unit argument (N2a, step 2).

For `q ≥ 2` and all `m, N : ℕ`, the geometric sum `q + q^2 + ⋯ + q^(m+1)`, multiplied by `q^N`,
dominates `m + q`:

    `m + 1 + (q - 1) ≤ (∑ i ∈ Finset.range (m+1), q^(i+1)) * q^N`.

Proof idea: `(∑ i ∈ Finset.range (m+1), q^(i+1)) ≥ q^(m+1)` (single-term lower bound), so it
suffices that `q^(m+1) * q^N ≥ m + q`.  Since `q^N ≥ 1`, `q^(m+1)·q^N ≥ q^(m+1)`, and
`q^(m+1) = q · q^m ≥ q · (m+1) = q·m + q ≥ m + q` once one has `q^m ≥ m + 1` (proved by induction on
`m`, base `q^0 = 1`, step `q^(m+1) = q·q^m ≥ 2·q^m ≥ 2(m+1) ≥ m+2`), using `q ≥ 2` and `1 ≤ q`.
-/
theorem geom_sum_mul_pow_ge {q m N : ℕ} (hq : 2 ≤ q) :
    m + 1 + (q - 1) ≤ (∑ i ∈ Finset.range (m + 1), q ^ (i + 1)) * q ^ N := by
  have hqpos : 0 < q := by omega
  -- `q^m ≥ m + 1`, by Mathlib's `Nat.lt_pow_self`.
  have hqm : m + 1 ≤ q ^ m := Nat.succ_le_of_lt (Nat.lt_pow_self (by omega))
  -- Single-term lower bound on the geometric sum: the `i = m` term is `q^(m+1)`.
  have hsum : q ^ (m + 1) ≤ ∑ i ∈ Finset.range (m + 1), q ^ (i + 1) := by
    refine Finset.single_le_sum (f := fun i => q ^ (i + 1)) (fun i _ => Nat.zero_le _) ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_self m)
  -- The geometric sum dominates `m + q`.
  have hpow : m + 1 + (q - 1) ≤ q ^ (m + 1) := by
    have h1 : m + 1 + (q - 1) = m + q := by omega
    rw [h1, pow_succ]
    calc m + q ≤ (m + 1) * q := by
          have : m ≤ m * q := Nat.le_mul_of_pos_right (m := q) m hqpos
          calc m + q ≤ m * q + q := Nat.add_le_add_right this q
            _ = (m + 1) * q := (Nat.succ_mul m q).symm
      _ ≤ q ^ m * q := Nat.mul_le_mul_right q hqm
  calc m + 1 + (q - 1) ≤ q ^ (m + 1) := hpow
    _ ≤ ∑ i ∈ Finset.range (m + 1), q ^ (i + 1) := hsum
    _ ≤ (∑ i ∈ Finset.range (m + 1), q ^ (i + 1)) * q ^ N := by
        have hN : 1 ≤ q ^ N := Nat.one_le_pow N q hqpos
        calc ∑ i ∈ Finset.range (m + 1), q ^ (i + 1)
            = (∑ i ∈ Finset.range (m + 1), q ^ (i + 1)) * 1 := (Nat.mul_one _).symm
          _ ≤ (∑ i ∈ Finset.range (m + 1), q ^ (i + 1)) * q ^ N :=
              Nat.mul_le_mul_left _ hN

end Commons.Combinatorics.Nat