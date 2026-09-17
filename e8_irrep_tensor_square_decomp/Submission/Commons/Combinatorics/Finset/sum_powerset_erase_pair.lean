import Submission.Commons.Combinatorics.Finset.sum_powerset_erase

namespace Commons.Combinatorics.Finset

open scoped BigOperators

/-- Two-fold version of `sum_powerset_erase`: summing over ordered pairs `(a, a')` of distinct
elements of `s` together with a subset `t` of `s.erase a` with `a' ∉ t` equals the sum over
subsets `T ⊆ s` together with ordered pairs `(a,a')` of distinct elements of `T`. -/
theorem sum_powerset_erase_pair {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (f : α → α → Finset α → β) :
    (∑ a ∈ s, ∑ a' ∈ s.erase a, ∑ t ∈ ((s.erase a).erase a').powerset, f a a' t)
      = ∑ T ∈ s.powerset, ∑ a ∈ T, ∑ a' ∈ T.erase a,
          f a a' ((T.erase a).erase a') := by
  calc (∑ a ∈ s, ∑ a' ∈ s.erase a, ∑ t ∈ ((s.erase a).erase a').powerset, f a a' t)
      = ∑ a ∈ s, ∑ T ∈ (s.erase a).powerset, ∑ a' ∈ T, f a a' (T.erase a') :=
        Finset.sum_congr rfl fun a _ => sum_powerset_erase (s.erase a) (f a)
    _ = ∑ T ∈ s.powerset, ∑ a ∈ T, ∑ a' ∈ T.erase a,
          f a a' ((T.erase a).erase a') :=
        sum_powerset_erase s (fun a T => ∑ a' ∈ T, f a a' (T.erase a'))

end Commons.Combinatorics.Finset
