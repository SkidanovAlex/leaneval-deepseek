import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Commons.Data.Nat.sum_digits_decomp
import Submission.Commons.Data.Nat.packed_mul3_block_le

namespace Commons.Data.Nat

open Finset
open scoped BigOperators

/-- **Sparse packed-block extraction.**  If `x : Fin n → ℕ` are the digits (all `< B`) of the
number `Σ j, x j * B ^ (s j)` written at the *sparse* (injective) positions `s j`, then the base-`B`
digit of that number at position `s i` is `x i`.  This is the sparse-position version of the
commons lemma `Commons.Data.Nat.packed_block`. -/
theorem packed_sparse_block {B n : ℕ} (hB : 1 < B) (s : Fin n → ℕ) (hs : Function.Injective s)
    (x : Fin n → ℕ) (hx : ∀ i, x i < B) (i : Fin n) :
    ((∑ j : Fin n, x j * B ^ (s j)) / B ^ (s i)) % B = x i := by
  classical
  have hB0 : 0 < B := by omega
  obtain ⟨L, hL⟩ : ∃ L, ∀ j : Fin n, s j < L :=
    ⟨(∑ j : Fin n, s j) + 1, fun j => by
      have h1 : s j ≤ ∑ j : Fin n, s j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega⟩
  set a : ℕ → ℕ := fun e => ∑ j ∈ Finset.univ.filter (fun j : Fin n => s j = e), x j with hadef
  have ha_lt : ∀ e < L, a e < B := by
    intro e _
    simp only [hadef]
    by_cases hne : (Finset.univ.filter (fun j : Fin n => s j = e)).Nonempty
    · obtain ⟨j0, hj0⟩ := hne
      have hmem : j0 ∈ Finset.univ.filter (fun j : Fin n => s j = e) := hj0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hset : Finset.univ.filter (fun j : Fin n => s j = e) = {j0} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun hj => hs (by rw [hj, hmem]), fun hj => by rw [hj, hmem]⟩
      rw [hset, Finset.sum_singleton]
      exact hx j0
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]
      exact hB0
  have hsum : (∑ j : Fin n, x j * B ^ (s j)) = ∑ e ∈ Finset.range L, a e * B ^ e := by
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range L)
      (g := fun j : Fin n => s j) (fun j _ => Finset.mem_range.mpr (hL j))
      (fun j : Fin n => x j * B ^ (s j))
    rw [← hfib]
    refine Finset.sum_congr rfl ?_
    intro e _
    simp only [hadef, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [hj]
  rw [hsum]
  have hdig := sum_digits_decomp (p := B) (L := L) a ha_lt (s i)
  rw [hdig, if_pos (hL i)]
  have hai : a (s i) = x i := by
    simp only [hadef]
    have hset : Finset.univ.filter (fun j : Fin n => s j = s i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hs h, fun h => by rw [h]⟩
    rw [hset, Finset.sum_singleton]
  rw [hai]

end Commons.Data.Nat