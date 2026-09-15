import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Analysis.Complex.Cartan

open scoped BigOperators

/-- **Counting rearrangement.** If for every `k ∈ [1, |S|]` fewer than `k` of the values `d i`
(`i ∈ S`) are `< r k`, then `∏_{k=1}^{|S|} r k ≤ ∏_{i∈S} d i`. -/
theorem prod_le_prod_of_card_filter_lt {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (d : ι → ℝ) (r : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (hr : ∀ k, 0 < r k)
    (h : ∀ k, 1 ≤ k → k ≤ S.card → (S.filter (fun i => d i < r k)).card ≤ k - 1) :
    ∏ k ∈ Finset.Icc 1 S.card, r k ≤ ∏ i ∈ S, d i := by
  classical
  suffices key : ∀ n, ∀ (T : Finset ι), T.card = n →
      (∀ i, 0 ≤ d i) → (∀ k, 0 < r k) →
      (∀ k, 1 ≤ k → k ≤ T.card → (T.filter (fun i => d i < r k)).card ≤ k - 1) →
      ∏ k ∈ Finset.Icc 1 T.card, r k ≤ ∏ i ∈ T, d i from
    key S.card S rfl hd hr h
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih T hT hd' hr' h'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Finset.card_eq_zero] at hT
    rw [hT]
    simp
  · have hnpos : 1 ≤ n := hn
    have hex : ∃ j ∈ T, r n ≤ d j := by
      by_contra hc
      simp only [not_exists, not_and, not_le] at hc
      have hfe : T.filter (fun i => d i < r n) = T :=
        Finset.filter_true_of_mem (fun i hi => hc i hi)
      have hbound := h' n hnpos (by rw [hT])
      rw [hfe, hT] at hbound
      omega
    obtain ⟨j, hjT, hjr⟩ := hex
    have hT'card : (T.erase j).card = n - 1 := by
      rw [Finset.card_erase_of_mem hjT, hT]
    have hnlt : n - 1 < n := by omega
    have hcond : ∀ k, 1 ≤ k → k ≤ (T.erase j).card →
        ((T.erase j).filter (fun i => d i < r k)).card ≤ k - 1 := by
      intro k hk1 hk2
      have hk2' : k ≤ T.card := by
        rw [hT'card] at hk2
        rw [hT]
        omega
      have hsub : (T.erase j).filter (fun i => d i < r k) ⊆
          T.filter (fun i => d i < r k) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨(Finset.mem_erase.mp hi.1).2, hi.2⟩
      exact le_trans (Finset.card_le_card hsub) (h' k hk1 hk2')
    have ih' := ih (n - 1) hnlt (T.erase j) hT'card hd' hr' hcond
    rw [hT'card] at ih'
    have hInmem : n ∉ Finset.Icc 1 (n - 1) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    have hIcc : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hCnneg : 0 ≤ ∏ k ∈ Finset.Icc 1 (n - 1), r k :=
      Finset.prod_nonneg fun k _ => le_of_lt (hr' k)
    have hmain : r n * (∏ k ∈ Finset.Icc 1 (n - 1), r k) ≤
        d j * (∏ i ∈ T.erase j, d i) :=
      mul_le_mul hjr ih' hCnneg (hd' j)
    calc ∏ k ∈ Finset.Icc 1 T.card, r k
        = ∏ k ∈ Finset.Icc 1 n, r k := by rw [hT]
      _ = r n * ∏ k ∈ Finset.Icc 1 (n - 1), r k := by
            rw [hIcc, Finset.prod_insert hInmem]
      _ ≤ d j * ∏ i ∈ T.erase j, d i := hmain
      _ = ∏ i ∈ T, d i := Finset.mul_prod_erase T d hjT

end Commons.Analysis.Complex.Cartan