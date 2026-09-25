import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_separator_of_pairwise_independent
import Submission.Commons.RingTheory.Valuation.valuation_sum_eq_of_unique_max

namespace Commons.RingTheory.Valuation

open scoped BigOperators

private theorem partition_helper {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ValuationSubring F) (hnt : ∀ i, A i ≠ ⊤)
    (hind : ∀ i j, i ≠ j → A i ⊔ A j = ⊤)
    (hne : Nonempty ι)
    (r : ∀ i, (A i).ValueGroup) (hr : ∀ i, 0 < r i) :
    ∃ e : ι → F, (∑ i, e i) = 1 ∧ ∀ i j, i ≠ j → (A i).valuation (e j) < r i := by
  classical
  let r' : ∀ i, (A i).ValueGroup := fun i => min (r i) 1
  have hr' : ∀ i, 0 < r' i := fun i => lt_min (hr i) zero_lt_one
  have hk : ∀ k, ∃ c : F, (A k).valuation c > 1 ∧ ∀ j, j ≠ k → (A j).valuation c < r' j := by
    intro k
    obtain ⟨x, hx1, hx2⟩ :=
      separator_aux A hnt hind k (Finset.univ.erase k) (Finset.notMem_erase k Finset.univ)
        1 zero_lt_one r' (fun j _ => hr' j)
    exact ⟨x, hx1, fun j hj => hx2 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)⟩
  choose c hc1 hc2 using hk
  let S : F := ∑ l, c l
  have hSval : ∀ i, (A i).valuation S = (A i).valuation (c i) := by
    intro i
    apply valuation_sum_eq_of_unique_max (s := Finset.univ) (f := c) (i₀ := i)
    · exact Finset.mem_univ i
    · intro l _ hli
      calc (A i).valuation (c l) < r' i := hc2 l i (fun h => hli h.symm)
        _ ≤ 1 := min_le_right _ _
        _ < (A i).valuation (c i) := hc1 i
  have hS_ne : S ≠ 0 := by
    intro hS0
    obtain ⟨i⟩ := hne
    have h := hSval i
    rw [hS0, Valuation.map_zero] at h
    exact (ne_of_gt (lt_trans zero_lt_one (hc1 i))) h.symm
  refine ⟨fun k => c k / S, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hS_ne]
  · intro i j hij
    rw [Valuation.map_div, hSval i]
    have hci1 : 1 < (A i).valuation (c i) := hc1 i
    have hcipos : 0 < (A i).valuation (c i) := lt_trans zero_lt_one hci1
    have h1 : (A i).valuation (c j) / (A i).valuation (c i) < r' i / (A i).valuation (c i) :=
      div_lt_div_of_pos_right (hc2 j i hij) hcipos
    have h2 : r' i / (A i).valuation (c i) < r' i := by
      rw [div_lt_iff₀ hcipos]
      exact lt_mul_of_one_lt_right (hr' i) hci1
    exact lt_of_lt_of_le (h1.trans h2) (min_le_left (r i) 1)

theorem exists_valuation_sub_lt_of_pairwise_independent {F : Type*} [Field F] {ι : Type*}
    [Fintype ι] (A : ι → ValuationSubring F) (hnt : ∀ i, A i ≠ ⊤)
    (hind : ∀ i j, i ≠ j → A i ⊔ A j = ⊤)
    (a : ι → F) (γ : ∀ i, (A i).ValueGroup) (hγ : ∀ i, 0 < γ i) :
    ∃ x : F, ∀ i, (A i).valuation (x - a i) < γ i := by
  classical
  by_cases hne : Nonempty ι
  · let M : ∀ i, (A i).ValueGroup :=
      fun i => (Finset.univ.erase i).sup (fun j => (A i).valuation (a j - a i))
    let c : ∀ i, (A i).ValueGroup := fun i => γ i / max 1 (M i)
    have hc : ∀ i, 0 < c i := by
      intro i
      exact div_pos (hγ i) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    obtain ⟨e, he1, he2⟩ := partition_helper A hnt hind hne c hc
    refine ⟨∑ j, a j * e j, ?_⟩
    intro i
    have hsub : (∑ j, a j * e j) - a i = ∑ j, (a j - a i) * e j := by
      have h1 : ∑ j, (a j - a i) * e j = ∑ j, (a j * e j - a i * e j) := by
        apply Finset.sum_congr rfl; intro j _; rw [sub_mul]
      rw [h1, Finset.sum_sub_distrib]
      have h2 : ∑ j, a i * e j = a i := by
        rw [← Finset.mul_sum, he1, mul_one]
      rw [h2]
    rw [hsub]
    have hterm : ∀ j, (A i).valuation ((a j - a i) * e j) < γ i := by
      intro j
      by_cases hji : j = i
      · rw [hji, sub_self, zero_mul, Valuation.map_zero]; exact hγ i
      · rw [Valuation.map_mul]
        by_cases haj : a j - a i = 0
        · rw [haj, Valuation.map_zero, zero_mul]; exact hγ i
        · have hpos : 0 < (A i).valuation (a j - a i) :=
            lt_of_le_of_ne' zero_le (fun h => haj ((Valuation.zero_iff (A i).valuation).mp h))
          have hmem : j ∈ Finset.univ.erase i := by simp [Finset.mem_erase, hji]
          have hle : (A i).valuation (a j - a i) ≤ M i := by
            show (A i).valuation (a j - a i) ≤
              (Finset.univ.erase i).sup (fun j => (A i).valuation (a j - a i))
            exact Finset.le_sup (f := fun j => (A i).valuation (a j - a i)) hmem
          have hej : (A i).valuation (e j) < c i := he2 i j (fun h => hji h.symm)
          calc (A i).valuation (a j - a i) * (A i).valuation (e j)
              < (A i).valuation (a j - a i) * c i := mul_lt_mul_of_pos_left hej hpos
            _ ≤ M i * c i := mul_le_mul_of_nonneg_right hle (le_of_lt (hc i))
            _ ≤ γ i := by
                have hX : 0 < max (1:(A i).ValueGroup) (M i) :=
                  lt_of_lt_of_le zero_lt_one (le_max_left _ _)
                have hMle : M i / max 1 (M i) ≤ 1 :=
                  (div_le_iff₀ hX).mpr (by rw [one_mul]; exact le_max_right _ _)
                show M i * (γ i / max 1 (M i)) ≤ γ i
                calc M i * (γ i / max 1 (M i)) = (M i / max 1 (M i)) * γ i := by
                      rw [mul_div_assoc', div_mul_eq_mul_div]
                  _ ≤ 1 * γ i := mul_le_mul_of_nonneg_right hMle (le_of_lt (hγ i))
                  _ = γ i := one_mul _
    refine lt_of_le_of_lt ((A i).valuation.map_sum_le
      (g := Finset.univ.sup (fun j => (A i).valuation ((a j - a i) * e j)))
      (fun j _ => Finset.le_sup (f := fun j => (A i).valuation ((a j - a i) * e j))
        (Finset.mem_univ j))) ?_
    exact (Finset.sup_lt_iff (hγ i)).mpr (fun j _ => hterm j)
  · refine ⟨0, ?_⟩
    intro i
    exact (hne ⟨i⟩).elim

end Commons.RingTheory.Valuation
