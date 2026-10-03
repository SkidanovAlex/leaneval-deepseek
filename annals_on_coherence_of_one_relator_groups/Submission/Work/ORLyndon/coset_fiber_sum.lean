import Mathlib
import Submission.Work.ORLyndon.cosetRepDefs
import Submission.Work.ORLyndon.cosetFinsetDefs

namespace Work.ORLyndon

/-- Summing `f` over the whole right coset `t⟨w⟩` agrees with summing `f` over those elements of
`s` that lie in that coset, when `f` vanishes off `s` and `t` is the chosen representative of a
coset that meets `s`. -/
theorem coset_fiber_sum {G : Type*} [Group G] [DecidableEq G] {K : Type*} [Field K]
    (w : G) (l : ℕ) (hpos : 1 ≤ l) (hw : w ^ l = 1) (f : G → K) (s : Finset G)
    (hsupp : ∀ x, x ∉ s → f x = 0) (t : G) (ht : t ∈ s.image (cosetRep w)) :
    (∑ h ∈ cosetFinset w l t, f h) = ∑ h ∈ s.filter (fun h => cosetRep w h = t), f h := by
  classical
  have hl : 0 < l := by omega
  -- `t` is a representative of its own coset.
  have ht_self : cosetRep w t = t := cosetRep_eq_self_of_mem_image ht
  -- Membership in the coset `t⟨w⟩` is exactly having `t` as chosen representative.
  have hiff : ∀ h : G, (cosetRep w h = t) ↔ h ∈ cosetFinset w l t := by
    intro h
    constructor
    · intro hh
      obtain ⟨m, hm⟩ := cosetRep_spec w h
      rw [mem_cosetFinset_iff hl hw]
      exact ⟨m, by rw [hm, hh]⟩
    · intro hh
      obtain ⟨m, hm⟩ := (mem_cosetFinset_iff hl hw).mp hh
      rw [← ht_self]
      exact (cosetRep_eq_of_sameRCoset ⟨m, hm⟩).symm
  -- The filtered finset is the intersection of `s` with the coset finset.
  have hfilter : s.filter (fun h => cosetRep w h = t) = s ∩ cosetFinset w l t := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_inter, hiff h]
  rw [hfilter]
  -- Inside the coset, the elements outside `s` contribute `0`.
  exact (Finset.sum_subset (Finset.inter_subset_right) (by
    intro x hxcoset hxnotin
    exact hsupp x (fun hxs => hxnotin (Finset.mem_inter.mpr ⟨hxs, hxcoset⟩)))).symm

end Work.ORLyndon
