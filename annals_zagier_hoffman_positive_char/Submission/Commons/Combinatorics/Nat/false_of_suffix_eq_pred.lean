import Mathlib
import Submission.Commons.Combinatorics.List.sum_range_eq_sum_range_succ_add_const
import Submission.Commons.Combinatorics.Nat.sum_range_eq_sum_range_of_eq_zero_of_le

namespace Commons.Combinatorics.Nat

/-- Auxiliary: if `e₁` and `e₂` agree below `K` but differ at `K`, have the same total
weight, `e₁` vanishes from `r₁` on and `e₂` is positive and vanishes from `r₂` on, then
necessarily `K < r₁`.  (Symmetrically `K < r₂`.) -/
private lemma lt_of_ne {w K r₁ r₂ : ℕ} {e₁ e₂ : ℕ → ℕ}
    (hpos₂ : ∀ j < r₂, 1 ≤ e₂ j)
    (hz₂ : ∀ j, r₂ ≤ j → e₂ j = 0)
    (hwt₁ : ∑ j ∈ Finset.range r₁, e₁ j = w)
    (hwt₂ : ∑ j ∈ Finset.range r₂, e₂ j = w)
    (hagree : ∀ l < K, e₁ l = e₂ l)
    (hne : e₁ K ≠ e₂ K)
    (hz₁ : ∀ j, r₁ ≤ j → e₁ j = 0) :
    K < r₁ := by
  by_contra h
  have hr₁K : r₁ ≤ K := Nat.le_of_not_lt h
  have he₁K : e₁ K = 0 := hz₁ K hr₁K
  have he₂K_ne : e₂ K ≠ 0 := fun h0 => hne (by rw [he₁K, h0])
  have hK₂ : K < r₂ := by
    by_contra h'
    exact he₂K_ne (hz₂ K (Nat.le_of_not_lt h'))
  have hsumK₁ : ∑ j ∈ Finset.range K, e₁ j = w := by
    rw [← hwt₁]
    exact (sum_range_eq_sum_range_of_eq_zero_of_le hr₁K hz₁).symm
  have hsumK₂ : ∑ j ∈ Finset.range K, e₂ j = ∑ j ∈ Finset.range K, e₁ j :=
    Finset.sum_congr rfl (fun j hj => (hagree j (Finset.mem_range.mp hj)).symm)
  have hsplit : ∑ j ∈ Finset.range (K + 1), e₂ j ≤ ∑ j ∈ Finset.range r₂, e₂ j := by
    calc ∑ j ∈ Finset.range (K + 1), e₂ j
        ≤ ∑ j ∈ Finset.range (K + 1), e₂ j
            + ∑ j ∈ Finset.range (r₂ - (K + 1)), e₂ ((K + 1) + j) := Nat.le_add_right _ _
      _ = ∑ j ∈ Finset.range ((K + 1) + (r₂ - (K + 1))), e₂ j :=
            (Finset.sum_range_add e₂ (K + 1) (r₂ - (K + 1))).symm
      _ = ∑ j ∈ Finset.range r₂, e₂ j := by
            rw [Nat.add_sub_of_le (Nat.succ_le_of_lt hK₂)]
  have h2 : ∑ j ∈ Finset.range K, e₂ j + 1 ≤ ∑ j ∈ Finset.range r₂, e₂ j := by
    have hsucc : ∑ j ∈ Finset.range (K + 1), e₂ j = ∑ j ∈ Finset.range K, e₂ j + e₂ K :=
      Finset.sum_range_succ e₂ K
    have hposK : 1 ≤ e₂ K := hpos₂ K hK₂
    calc ∑ j ∈ Finset.range K, e₂ j + 1
        ≤ ∑ j ∈ Finset.range K, e₂ j + e₂ K := Nat.add_le_add_left hposK _
      _ = ∑ j ∈ Finset.range (K + 1), e₂ j := hsucc.symm
      _ ≤ ∑ j ∈ Finset.range r₂, e₂ j := hsplit
  have : w + 1 ≤ w := by
    calc w + 1 = ∑ j ∈ Finset.range K, e₂ j + 1 := by rw [hsumK₂, hsumK₁]
      _ ≤ ∑ j ∈ Finset.range r₂, e₂ j := h2
      _ = w := hwt₂
  exact Nat.not_succ_le_self w this

theorem false_of_suffix_eq_pred {q w K : ℕ} (hq : 2 ≤ q) {r₁ : ℕ} {e₁ : ℕ → ℕ} {r₂ : ℕ} {e₂ : ℕ → ℕ} (hpos₁ : ∀ j < r₁, 1 ≤ e₁ j) (hpos₂ : ∀ j < r₂, 1 ≤ e₂ j) (hlt₁ : ∀ j < r₁, e₁ j < q) (hlt₂ : ∀ j < r₂, e₂ j < q) (hz₁ : ∀ j, r₁ ≤ j → e₁ j = 0) (hz₂ : ∀ j, r₂ ≤ j → e₂ j = 0) (hwt₁ : ∑ j ∈ Finset.range r₁, e₁ j = w) (hwt₂ : ∑ j ∈ Finset.range r₂, e₂ j = w) (hagree : ∀ l < K, e₁ l = e₂ l) (hnotagree : ¬ ∀ l < K + 1, e₁ l = e₂ l) (hdiv₁ : ∀ j, K < j → j < r₁ → e₁ j = q - 1) (hdiv₂ : ∀ j, K < j → j < r₂ → e₂ j = q - 1) : False := by
  have hne : e₁ K ≠ e₂ K := by
    intro hcon
    apply hnotagree
    intro l hl
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hl) with hlt | rfl
    · exact hagree l hlt
    · exact hcon
  have hK₁ : K < r₁ := lt_of_ne hpos₂ hz₂ hwt₁ hwt₂ hagree hne hz₁
  have hK₂ : K < r₂ := lt_of_ne hpos₁ hz₁ hwt₂ hwt₁ (fun l hl => (hagree l hl).symm) hne.symm hz₂
  have hdec₁ := Commons.Combinatorics.List.sum_range_eq_sum_range_succ_add_const e₁ hK₁ hdiv₁
  have hdec₂ := Commons.Combinatorics.List.sum_range_eq_sum_range_succ_add_const e₂ hK₂ hdiv₂
  have heq1 : w = (∑ j ∈ Finset.range K, e₁ j) + (e₁ K + (r₁ - (K + 1)) * (q - 1)) := by
    rw [← hwt₁, hdec₁, Finset.sum_range_succ, Nat.add_assoc]
  have heq2 : w = (∑ j ∈ Finset.range K, e₂ j) + (e₂ K + (r₂ - (K + 1)) * (q - 1)) := by
    rw [← hwt₂, hdec₂, Finset.sum_range_succ, Nat.add_assoc]
  have hA : ∑ j ∈ Finset.range K, e₁ j = ∑ j ∈ Finset.range K, e₂ j :=
    Finset.sum_congr rfl (fun j hj => hagree j (Finset.mem_range.mp hj))
  have heq : e₁ K + (r₁ - (K + 1)) * (q - 1) = e₂ K + (r₂ - (K + 1)) * (q - 1) := by
    have hh := heq1.symm.trans heq2
    rw [hA] at hh
    exact Nat.add_left_cancel hh
  rcases le_total (r₁ - (K + 1)) (r₂ - (K + 1)) with hmn | hnm
  · -- r₁ - (K+1) ≤ r₂ - (K+1)
    have heq' : e₁ K + (r₁ - (K + 1)) * (q - 1)
        = e₂ K + ((r₁ - (K + 1)) + ((r₂ - (K + 1)) - (r₁ - (K + 1)))) * (q - 1) := by
      rw [← Nat.add_sub_of_le hmn] at heq
      exact heq
    have key : e₁ K = e₂ K + ((r₂ - (K + 1)) - (r₁ - (K + 1))) * (q - 1) := by
      refine Nat.add_right_cancel (m := (r₁ - (K + 1)) * (q - 1)) ?_
      show e₁ K + (r₁ - (K + 1)) * (q - 1)
          = (e₂ K + ((r₂ - (K + 1)) - (r₁ - (K + 1))) * (q - 1))
              + (r₁ - (K + 1)) * (q - 1)
      rw [heq']; ring
    have hsub : e₁ K - e₂ K = ((r₂ - (K + 1)) - (r₁ - (K + 1))) * (q - 1) := by omega
    have hbound : e₁ K - e₂ K ≤ q - 2 := by
      have h1 : e₁ K ≤ q - 1 := by have := hlt₁ K hK₁; omega
      have h2 : 1 ≤ e₂ K := hpos₂ K hK₂
      omega
    have hqle : ((r₂ - (K + 1)) - (r₁ - (K + 1))) * (q - 1) ≤ q - 2 := by
      rw [← hsub]; exact hbound
    have hd0 : (r₂ - (K + 1)) - (r₁ - (K + 1)) = 0 := by
      have hlt : ((r₂ - (K + 1)) - (r₁ - (K + 1))) * (q - 1) < q - 1 := by omega
      by_contra hne0
      have h1 : 1 ≤ (r₂ - (K + 1)) - (r₁ - (K + 1)) := by omega
      have hle : q - 1 ≤ ((r₂ - (K + 1)) - (r₁ - (K + 1))) * (q - 1) := by
        have := Nat.mul_le_mul_right (q - 1) h1
        simpa using this
      omega
    exact hne (by rw [key, hd0, zero_mul, add_zero])
  · -- r₂ - (K+1) ≤ r₁ - (K+1)
    have heq' : e₁ K + ((r₂ - (K + 1)) + ((r₁ - (K + 1)) - (r₂ - (K + 1)))) * (q - 1)
        = e₂ K + (r₂ - (K + 1)) * (q - 1) := by
      rw [← Nat.add_sub_of_le hnm] at heq
      exact heq
    have key : e₂ K = e₁ K + ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1) := by
      refine (Nat.add_right_cancel (m := (r₂ - (K + 1)) * (q - 1)) ?_).symm
      show (e₁ K + ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1))
              + (r₂ - (K + 1)) * (q - 1)
          = e₂ K + (r₂ - (K + 1)) * (q - 1)
      rw [show (e₁ K + ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1))
                + (r₂ - (K + 1)) * (q - 1)
              = e₁ K + ((r₂ - (K + 1)) + ((r₁ - (K + 1)) - (r₂ - (K + 1)))) * (q - 1)
            by ring]
      exact heq'
    have hsub : e₂ K - e₁ K = ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1) := by omega
    have hbound : e₂ K - e₁ K ≤ q - 2 := by
      have h1 : e₂ K ≤ q - 1 := by have := hlt₂ K hK₂; omega
      have h2 : 1 ≤ e₁ K := hpos₁ K hK₁
      omega
    have hqle : ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1) ≤ q - 2 := by
      rw [← hsub]; exact hbound
    have hd0 : (r₁ - (K + 1)) - (r₂ - (K + 1)) = 0 := by
      have hlt : ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1) < q - 1 := by omega
      by_contra hne0
      have h1 : 1 ≤ (r₁ - (K + 1)) - (r₂ - (K + 1)) := by omega
      have hle : q - 1 ≤ ((r₁ - (K + 1)) - (r₂ - (K + 1))) * (q - 1) := by
        have := Nat.mul_le_mul_right (q - 1) h1
        simpa using this
      omega
    have : e₂ K = e₁ K := by rw [key, hd0, zero_mul, add_zero]
    exact hne this.symm

end Commons.Combinatorics.Nat
