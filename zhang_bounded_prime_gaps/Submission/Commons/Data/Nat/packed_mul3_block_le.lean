import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Commons.Data.Nat.sum_digits_decomp

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.Data.Nat

/-- The product of three packed integers expands as the triple sum of the digit
products times the corresponding powers of `B`. -/
private lemma triple_prod_eq_sum {B n m l : ℕ} (x y z : ℕ → ℕ) :
    ((∑ i ∈ Finset.range n, x i * B ^ i) * (∑ j ∈ Finset.range m, y j * B ^ j)
      * (∑ k ∈ Finset.range l, z k * B ^ k))
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          x i * y j * z k * B ^ (i + j + k) := by
  have hXY : (∑ i ∈ Finset.range n, x i * B ^ i) * (∑ j ∈ Finset.range m, y j * B ^ j)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, x i * y j * B ^ (i + j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    calc x i * B ^ i * (y j * B ^ j)
        = x i * y j * (B ^ i * B ^ j) := by ring
      _ = x i * y j * B ^ (i + j) := by rw [pow_add]
  rw [hXY, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  calc x i * y j * B ^ (i + j) * (z k * B ^ k)
      = x i * y j * z k * (B ^ (i + j) * B ^ k) := by ring
    _ = x i * y j * z k * B ^ (i + j + k) := by rw [← pow_add]

/-- The product of the (plain) sums equals the triple sum of the products. -/
private lemma triple_sum_plain {n m l : ℕ} (x y z : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, x i) * (∑ j ∈ Finset.range m, y j)
        * (∑ k ∈ Finset.range l, z k)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          x i * y j * z k := by
  have h := triple_prod_eq_sum (B := 1) (n := n) (m := m) (l := l) x y z
  simpa using h

/-- Regrouping a triple sum by the value of `i + j + k`, all exponents being `< L`. -/
private lemma triple_sum_grouped {B n m l L : ℕ} (x y z : ℕ → ℕ)
    (hL : ∀ i, i < n → ∀ j, j < m → ∀ k, k < l → i + j + k < L) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
        x i * y j * z k * B ^ (i + j + k))
      = ∑ s ∈ Finset.range L,
          (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
            if i + j + k = s then x i * y j * z k else 0) * B ^ s := by
  symm
  calc ∑ s ∈ Finset.range L,
          (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
            if i + j + k = s then x i * y j * z k else 0) * B ^ s
      = ∑ s ∈ Finset.range L, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
            ∑ k ∈ Finset.range l,
          (if i + j + k = s then x i * y j * z k else 0) * B ^ s := by
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
    _ = ∑ s ∈ Finset.range L, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
            ∑ k ∈ Finset.range l,
          (if i + j + k = s then x i * y j * z k * B ^ s else 0) := by
        refine Finset.sum_congr rfl ?_
        intro s _
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ite_mul, zero_mul]
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
            ∑ s ∈ Finset.range L,
          (if i + j + k = s then x i * y j * z k * B ^ s else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          x i * y j * z k * B ^ (i + j + k) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        refine Finset.sum_congr rfl ?_
        intro j hj
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [Finset.sum_ite_eq,
          if_pos (Finset.mem_range.mpr
            (hL i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) k
              (Finset.mem_range.mp hk)))]

theorem packed_mul3_block_le {B : ℕ} (hB : 1 < B) {n m l : ℕ} (x y z : ℕ → ℕ)
    (hxy : (∑ i ∈ Finset.range n, x i) * (∑ j ∈ Finset.range m, y j) < B)
    (h : (∑ i ∈ Finset.range n, x i) * (∑ j ∈ Finset.range m, y j)
        * (∑ k ∈ Finset.range l, z k) < B) (K : ℕ) :
    (((∑ i ∈ Finset.range n, x i * B ^ i) * (∑ j ∈ Finset.range m, y j * B ^ j)
        * (∑ k ∈ Finset.range l, z k * B ^ k)) / B ^ K) % B
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          if i + j + k = K then x i * y j * z k else 0 := by
  have hcoef : ∀ s, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
      ∑ k ∈ Finset.range l, if i + j + k = s then x i * y j * z k else 0) < B := by
    intro s
    have hle : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
        if i + j + k = s then x i * y j * z k else 0)
        ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          x i * y j * z k := by
      refine Finset.sum_le_sum ?_
      intro i _
      refine Finset.sum_le_sum ?_
      intro j _
      refine Finset.sum_le_sum ?_
      intro k _
      by_cases hc : i + j + k = s
      · rw [if_pos hc]
      · rw [if_neg hc]; exact Nat.zero_le _
    calc (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          if i + j + k = s then x i * y j * z k else 0)
        ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
          x i * y j * z k := hle
      _ = (∑ i ∈ Finset.range n, x i) * (∑ j ∈ Finset.range m, y j)
          * (∑ k ∈ Finset.range l, z k) := (triple_sum_plain x y z).symm
      _ < B := h
  have hL : ∀ i, i < n → ∀ j, j < m → ∀ k, k < l → i + j + k < n + m + l := by
    intro i hi j hj k hk
    omega
  rw [triple_prod_eq_sum, triple_sum_grouped x y z hL]
  rw [sum_digits_decomp (p := B) (L := n + m + l)
    (a := fun s => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range l,
        if i + j + k = s then x i * y j * z k else 0)
    (fun s _ => hcoef s) K]
  by_cases hK : K < n + m + l
  · rw [if_pos hK]
  · rw [if_neg hK]
    symm
    refine Finset.sum_eq_zero ?_
    intro i hi
    refine Finset.sum_eq_zero ?_
    intro j hj
    refine Finset.sum_eq_zero ?_
    intro k hk
    rw [if_neg (by
      intro hcon
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hk' := Finset.mem_range.mp hk
      omega)]

end Commons.Data.Nat