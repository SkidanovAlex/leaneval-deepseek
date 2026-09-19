import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Commons.Data.Nat.sum_digits_decomp

namespace Commons.Data.Nat

open Finset
open scoped BigOperators

/-- **Sparse packed-block vanishing.**  If the position `k` is not one of the (injective) sparse
positions `s j` at which the digits `x : Fin n → ℕ` (all `< B`) are written, then the base-`B`
digit of `Σ j, x j * B ^ (s j)` at position `k` is `0`.  This is the "no interference" half of the
sparse packed-block lemma. -/
theorem packed_sparse_block_zero {B n : ℕ} (hB : 1 < B) (s : Fin n → ℕ)
    (hs : Function.Injective s) (x : Fin n → ℕ) (hx : ∀ i, x i < B) (k : ℕ)
    (hk : ∀ i, s i ≠ k) :
    ((∑ j : Fin n, x j * B ^ (s j)) / B ^ k) % B = 0 := by
  classical
  have hB0 : 0 < B := by omega
  -- `L` bounds every sparse position `s j`.
  set L : ℕ := (∑ j : Fin n, s j) + 1 with hLdef
  have hle : ∀ j : Fin n, s j < L := by
    intro j
    have h1 : s j ≤ ∑ j : Fin n, s j :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [hLdef]; omega
  -- The full digit vector of the sparse packing: value `x j` at position `s j`, else `0`.
  set a : ℕ → ℕ :=
    fun i => if h : ∃ j : Fin n, s j = i then x (Classical.choose h) else 0 with hadef
  have ha_apply : ∀ i, a i = (if h : ∃ j : Fin n, s j = i then x (Classical.choose h) else 0) :=
    fun i => by rw [hadef]
  have ha_lt : ∀ i, a i < B := by
    intro i
    rw [ha_apply i]
    by_cases h : ∃ j : Fin n, s j = i
    · rw [dif_pos h]; exact hx _
    · rw [dif_neg h]; omega
  have ha_s : ∀ j : Fin n, a (s j) = x j := by
    intro j
    have hj : ∃ j' : Fin n, s j' = s j := ⟨j, rfl⟩
    rw [ha_apply (s j), dif_pos hj]
    have hc : Classical.choose hj = j := hs (Classical.choose_spec hj)
    rw [hc]
  have ha_k : a k = 0 := by
    rw [ha_apply k, dif_neg]
    rintro ⟨j, hj⟩
    exact hk j hj
  -- Reindex the sparse sum as a full range sum.
  have hreindex : (∑ j : Fin n, x j * B ^ (s j)) = ∑ i ∈ Finset.range L, a i * B ^ i := by
    calc ∑ j : Fin n, x j * B ^ (s j)
        = ∑ j : Fin n, a (s j) * B ^ (s j) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [ha_s j]
      _ = ∑ i ∈ Finset.univ.image s, a i * B ^ i := by
            exact (Finset.sum_image (f := fun i => a i * B ^ i)
              (fun u _ v _ huv => hs huv)).symm
      _ = ∑ i ∈ Finset.range L, a i * B ^ i := by
            refine Finset.sum_subset ?_ ?_
            · intro i hi
              obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
              exact Finset.mem_range.mpr (hle j)
            · intro i _ hni
              have hai : a i = 0 := by
                rw [ha_apply i, dif_neg]
                rintro ⟨j, hj⟩
                exact hni (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
              rw [hai, zero_mul]
  rw [hreindex]
  rw [Commons.Data.Nat.sum_digits_decomp (p := B) (L := L) (a := a)
        (fun i _ => ha_lt i) k]
  rw [ha_k]
  split <;> rfl

end Commons.Data.Nat