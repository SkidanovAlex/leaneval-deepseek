import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Commons.Data.Nat.geom_pred_mul_sum

open scoped BigOperators

set_option linter.unusedVariables false

namespace Commons.Data.Nat

/-- `q ^ j` is one of the summands of the geometric sum `∑_{i < m} q ^ i`. -/
lemma geom_sum_pow_le (q m j : ℕ) (hj : j < m) :
    q ^ j ≤ ∑ i ∈ Finset.range m, q ^ i :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)

/-- The sum of two distinct powers `q ^ a + q ^ b`, with `a, b < m`, is bounded by the
geometric sum `∑_{i < m} q ^ i`. -/
lemma geom_sum_pow_add_pow_le (q m a b : ℕ) (ha : a < m) (hb : b < m) (hab : a ≠ b) :
    q ^ a + q ^ b ≤ ∑ i ∈ Finset.range m, q ^ i := by
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.range m := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr ha
    · exact Finset.mem_range.mpr hb
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => q ^ i) hsub
    (fun i _ _ => Nat.zero_le (q ^ i))
  rwa [Finset.sum_pair hab] at h

theorem sum_mul_pow_le_compl_shift {q n s : ℕ} (hq : 2 ≤ q) (hs : 1 ≤ s) (N : ℕ → ℕ)
    (hN : ∀ i, i < n → N i ≤ q - 1)
    (hsum : ∑ i ∈ Finset.range n, N i ≤ q - 1) :
    ∑ i ∈ Finset.range (n - s), N i * q ^ i
      ≤ ∑ i ∈ Finset.range (n - s), (q - 1 - N (i + s)) * q ^ i := by
  by_cases hns : n ≤ s
  · have h0 : n - s = 0 := Nat.sub_eq_zero_of_le hns
    rw [h0]
    simp
  · have hsle : s ≤ n := le_of_lt (Nat.lt_of_not_le hns)
    set m : ℕ := n - s with hm
    have hms : m + s = n := by rw [hm]; exact Nat.sub_add_cancel hsle
    have hsum' : ∑ i ∈ Finset.range (m + s), N i ≤ q - 1 := by rw [hms]; exact hsum
    have hNle : ∀ i, i < m → N (i + s) ≤ q - 1 :=
      fun i hi => hN (i + s) (by rw [← hms]; omega)
    set S : ℕ := ∑ i ∈ Finset.range m, q ^ i with hS
    -- Reindexing `L` over `range (m + s)`.
    have eq1 : (∑ i ∈ Finset.range m, N i * q ^ i)
        = ∑ j ∈ Finset.range (m + s), (if j < m then N j * q ^ j else 0) := by
      have hsub : Finset.range m ⊆ Finset.range (m + s) := by
        intro j hj
        rw [Finset.mem_range] at hj ⊢
        omega
      have h1 : ∑ j ∈ Finset.range m, (if j < m then N j * q ^ j else 0)
          = ∑ j ∈ Finset.range (m + s), (if j < m then N j * q ^ j else 0) :=
        Finset.sum_subset hsub (fun x _ hxnm => by
          simp only [Finset.mem_range] at hxnm
          simp only [if_neg hxnm])
      have h2 : ∑ j ∈ Finset.range m, (if j < m then N j * q ^ j else 0)
          = ∑ j ∈ Finset.range m, N j * q ^ j :=
        Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj)])
      exact h2.symm.trans h1
    -- Reindexing `T` (the shifted sum) over `range (m + s)`.
    have eq2 : (∑ i ∈ Finset.range m, N (i + s) * q ^ i)
        = ∑ j ∈ Finset.range (m + s), (if s ≤ j then N j * q ^ (j - s) else 0) := by
      have himg : (Finset.range m).image (fun i => i + s)
          = (Finset.range (m + s)).filter (fun j => s ≤ j) := by
        ext j
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨by omega, by omega⟩
        · rintro ⟨hj, hsj⟩
          exact ⟨j - s, by omega, by omega⟩
      have hinj : Set.InjOn (fun i : ℕ => i + s) ↑(Finset.range m) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe] at ha hb
        simp only at hab
        omega
      have hf := Finset.sum_filter (s := Finset.range (m + s))
        (p := fun j => s ≤ j) (f := fun j => N j * q ^ (j - s))
      rw [← hf, ← himg, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_sub_cancel]
    -- Pointwise bound: the `j`-th "slot" carries total weight at most `S`.
    have hper : ∀ j, j < m + s →
        (if j < m then N j * q ^ j else 0) + (if s ≤ j then N j * q ^ (j - s) else 0)
          ≤ N j * S := by
      intro j hj
      by_cases hjm : j < m
      · by_cases hsj : s ≤ j
        · rw [if_pos hjm, if_pos hsj]
          have h1 : q ^ j + q ^ (j - s) ≤ S := by
            rw [hS]
            exact geom_sum_pow_add_pow_le q m j (j - s) hjm (by omega) (by omega)
          calc N j * q ^ j + N j * q ^ (j - s)
              = N j * (q ^ j + q ^ (j - s)) := (Nat.mul_add _ _ _).symm
            _ ≤ N j * S := Nat.mul_le_mul_left (N j) h1
        · rw [if_pos hjm, if_neg hsj]
          have h1 : q ^ j ≤ S := by rw [hS]; exact geom_sum_pow_le q m j hjm
          calc N j * q ^ j + 0 = N j * q ^ j := by rw [add_zero]
            _ ≤ N j * S := Nat.mul_le_mul_left (N j) h1
      · by_cases hsj : s ≤ j
        · rw [if_neg hjm, if_pos hsj]
          have h1 : q ^ (j - s) ≤ S := by
            rw [hS]; exact geom_sum_pow_le q m (j - s) (by omega)
          calc 0 + N j * q ^ (j - s) = N j * q ^ (j - s) := by rw [zero_add]
            _ ≤ N j * S := Nat.mul_le_mul_left (N j) h1
        · rw [if_neg hjm, if_neg hsj]
          exact Nat.zero_le _
    -- Core inequality: `L + T ≤ (q - 1) * S`.
    have hmain : (∑ i ∈ Finset.range m, N i * q ^ i)
        + (∑ i ∈ Finset.range m, N (i + s) * q ^ i) ≤ (q - 1) * S := by
      calc (∑ i ∈ Finset.range m, N i * q ^ i) + (∑ i ∈ Finset.range m, N (i + s) * q ^ i)
          = (∑ j ∈ Finset.range (m + s), (if j < m then N j * q ^ j else 0))
            + (∑ j ∈ Finset.range (m + s), (if s ≤ j then N j * q ^ (j - s) else 0)) := by
              rw [eq1, eq2]
        _ = ∑ j ∈ Finset.range (m + s),
              ((if j < m then N j * q ^ j else 0) + (if s ≤ j then N j * q ^ (j - s) else 0)) :=
              (Finset.sum_add_distrib).symm
        _ ≤ ∑ j ∈ Finset.range (m + s), N j * S :=
              Finset.sum_le_sum (fun j hj => hper j (Finset.mem_range.mp hj))
        _ = (∑ j ∈ Finset.range (m + s), N j) * S := (Finset.sum_mul _ _ _).symm
        _ ≤ (q - 1) * S := Nat.mul_le_mul_right S hsum'
    -- `RHS + T = (q - 1) * S`.
    have hRHSplusT : (∑ i ∈ Finset.range m, (q - 1 - N (i + s)) * q ^ i)
        + (∑ i ∈ Finset.range m, N (i + s) * q ^ i) = (q - 1) * S := by
      rw [← Finset.sum_add_distrib]
      have hpoint : ∀ i ∈ Finset.range m,
          (q - 1 - N (i + s)) * q ^ i + N (i + s) * q ^ i = (q - 1) * q ^ i := by
        intro i hi
        have hle := hNle i (Finset.mem_range.mp hi)
        rw [← Nat.add_mul, Nat.sub_add_cancel hle]
      rw [Finset.sum_congr rfl hpoint, hS, Finset.mul_sum]
    -- Conclude `L ≤ RHS`.
    rw [← hRHSplusT] at hmain
    exact (Nat.add_le_add_iff_right).mp hmain

end Commons.Data.Nat