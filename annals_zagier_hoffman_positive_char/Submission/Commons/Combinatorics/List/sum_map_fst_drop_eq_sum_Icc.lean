import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Nat

namespace Commons.Combinatorics.List

/-- For a list of naturals, its sum equals the sum of its entries read off by index,
where a missing index contributes `0`. -/
private lemma sum_eq_sum_range_getD (N : List ℕ) :
    N.sum = ∑ i ∈ Finset.range N.length, N[i]?.getD 0 := by
  induction N with
  | nil => simp
  | cons a t ih =>
      rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [Nat.add_comm]

/-- The sum of the entries of `M.drop k` equals the sum of the entries of `M` over the
indices `k, …, M.length - 1`. -/
private lemma sum_drop_eq_sum_Icc (M : List ℕ) (k : ℕ) :
    (M.drop k).sum = ∑ i ∈ Finset.Icc k (M.length - 1), M[i]?.getD 0 := by
  rw [sum_eq_sum_range_getD]
  simp only [List.length_drop, List.getElem?_drop]
  rw [← Finset.sum_Ico_eq_sum_range (fun i => M[i]?.getD 0) k M.length]
  cases hM : M.length with
  | zero =>
      have hnil : M = [] := List.eq_nil_of_length_eq_zero hM
      subst hnil
      simp
  | succ m =>
      have hpred : (m + 1) - 1 = m := by omega
      rw [hpred, Finset.Ico_add_one_right_eq_Icc]

theorem sum_map_fst_drop_eq_sum_Icc {α : Type*} (L : List (ℕ × α)) (k : ℕ) :
    ((L.drop k).map Prod.fst).sum = ∑ i ∈ Finset.Icc k (L.length - 1), ((L[i]?).map Prod.fst).getD 0 := by
  have h := sum_drop_eq_sum_Icc (L.map Prod.fst) k
  simpa [List.length_map, List.getElem?_map] using h

end Commons.Combinatorics.List