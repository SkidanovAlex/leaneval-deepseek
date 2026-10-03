import Mathlib

namespace Work.ORHughesFree.NaturalExtension

/-- Integer-interval sum splitting: if `A : ℤ → M` vanishes outside `[a, b]`, then subtracting
the sum over `[p, q]` from the sum over `[a, b]` leaves the sum over the low part `[a, p-1]` plus
the sum over the high part `[q+1, b]`.  (Requires `p ≤ q+1` so that the two remaining intervals
are disjoint; for `p ≥ q+2` they overlap and the identity fails, e.g. `a=0,b=10,p=5,q=3`
with `A ≡ 1` on `[0,10]`.) -/
theorem sum_Icc_sub_sum_Icc {M : Type*} [AddCommGroup M] (A : ℤ → M) (a b p q : ℤ)
    (hpq : p ≤ q + 1) (hvan : ∀ v : ℤ, v < a ∨ b < v → A v = 0) :
    (∑ v ∈ Finset.Icc a b, A v) - (∑ v ∈ Finset.Icc p q, A v)
      = (∑ v ∈ Finset.Icc a (p - 1), A v) + (∑ v ∈ Finset.Icc (q + 1) b, A v) := by
  -- Restricting a sum over an arbitrary interval to its intersection with `[a, b]` is harmless,
  -- because `A` vanishes outside `[a, b]`.
  have hres : ∀ s : Finset ℤ, (∑ v ∈ Finset.Icc a b ∩ s, A v) = ∑ v ∈ s, A v := by
    intro s
    refine Finset.sum_subset Finset.inter_subset_right ?_
    intro x hx hxnot
    apply hvan x
    have hxab : x ∉ Finset.Icc a b := fun h => hxnot (Finset.mem_inter.mpr ⟨h, hx⟩)
    rw [Finset.mem_Icc, not_and_or] at hxab
    rcases hxab with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  -- Pointwise version of the identity on `[a, b]`.
  have hkey : ∀ v ∈ Finset.Icc a b,
      A v - (if v ∈ Finset.Icc p q then A v else 0)
        = (if v ∈ Finset.Icc a (p - 1) then A v else 0)
          + (if v ∈ Finset.Icc (q + 1) b then A v else 0) := by
    intro v hv
    by_cases hm : v ∈ Finset.Icc p q
    · have hl : v ∉ Finset.Icc a (p - 1) := by
        rw [Finset.mem_Icc] at hm ⊢; omega
      have hh : v ∉ Finset.Icc (q + 1) b := by
        rw [Finset.mem_Icc] at hm ⊢; omega
      rw [if_pos hm, if_neg hl, if_neg hh, sub_self, zero_add]
    · by_cases hl : v ∈ Finset.Icc a (p - 1)
      · have hh : v ∉ Finset.Icc (q + 1) b := by
          rw [Finset.mem_Icc] at hl ⊢; omega
        rw [if_neg hm, if_pos hl, if_neg hh, sub_zero, add_zero]
      · have hh : v ∈ Finset.Icc (q + 1) b := by
          rw [Finset.mem_Icc] at hv hm hl ⊢
          exact ⟨by omega, by omega⟩
        rw [if_neg hm, if_neg hl, if_pos hh, sub_zero, zero_add]
  calc
    (∑ v ∈ Finset.Icc a b, A v) - (∑ v ∈ Finset.Icc p q, A v)
        = (∑ v ∈ Finset.Icc a b, A v)
            - (∑ v ∈ Finset.Icc a b ∩ Finset.Icc p q, A v) := by rw [← hres (Finset.Icc p q)]
    _ = (∑ v ∈ Finset.Icc a b, A v)
            - (∑ v ∈ Finset.Icc a b, if v ∈ Finset.Icc p q then A v else 0) := by
          rw [← Finset.sum_ite_mem]
    _ = ∑ v ∈ Finset.Icc a b, (A v - (if v ∈ Finset.Icc p q then A v else 0)) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ v ∈ Finset.Icc a b,
          ((if v ∈ Finset.Icc a (p - 1) then A v else 0)
            + (if v ∈ Finset.Icc (q + 1) b then A v else 0)) :=
          Finset.sum_congr rfl hkey
    _ = (∑ v ∈ Finset.Icc a b, (if v ∈ Finset.Icc a (p - 1) then A v else 0))
          + (∑ v ∈ Finset.Icc a b, (if v ∈ Finset.Icc (q + 1) b then A v else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ v ∈ Finset.Icc a b ∩ Finset.Icc a (p - 1), A v)
          + (∑ v ∈ Finset.Icc a b ∩ Finset.Icc (q + 1) b, A v) := by
          rw [Finset.sum_ite_mem, Finset.sum_ite_mem]
    _ = (∑ v ∈ Finset.Icc a (p - 1), A v)
          + (∑ v ∈ Finset.Icc (q + 1) b, A v) := by
          rw [hres (Finset.Icc a (p - 1)), hres (Finset.Icc (q + 1) b)]

end Work.ORHughesFree.NaturalExtension
