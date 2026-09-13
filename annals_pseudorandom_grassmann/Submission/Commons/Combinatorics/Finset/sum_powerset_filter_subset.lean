import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Powerset

namespace Commons.Combinatorics.Finset

theorem sum_powerset_filter_subset {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (S R : Finset ι) (f : Finset ι → M) :
    (∑ T ∈ S.powerset.filter (fun T => T ⊆ R), f T) = ∑ T ∈ (S ∩ R).powerset, f T := by
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]

end Commons.Combinatorics.Finset