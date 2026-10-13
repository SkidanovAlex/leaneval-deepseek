import Mathlib

namespace Work.WilG4c

/-- The multiset of a list `M` is the sum, over all `i : Fin n`, of `count i M` copies of
`{i}`: the "count vector" expansion of `M`. -/
theorem countvec_sum {n : ℕ} (M : List (Fin n)) :
    (Finset.univ.sum (fun i : Fin n =>
        (Multiset.ofList M).count i • ({i} : Multiset (Fin n)))) = (Multiset.ofList M) := by
  classical
  -- Only the indices actually occurring in `M` can contribute; the rest carry the coefficient
  -- `0` and contribute `0`.
  rw [← Finset.sum_subset (Finset.subset_univ (Multiset.ofList M).toFinset)
    (fun x _ hx => by
      rw [Multiset.mem_toFinset] at hx
      rw [Multiset.count_eq_zero.mpr hx, zero_nsmul])]
  exact Multiset.toFinset_sum_count_nsmul_eq _

theorem countvec_perm {n r : ℕ} (M : List (Fin n)) (hM : M.length ≤ r) :
    M.Perm ((Finset.univ.sum (fun i : Fin n =>
        (Multiset.ofList M).count i • ({i} : Multiset (Fin n)))).toList) := by
  rw [countvec_sum M]
  exact Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList])

end Work.WilG4c
