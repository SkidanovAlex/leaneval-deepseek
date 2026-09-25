import Mathlib

namespace Commons.Algebra.Module

lemma range_sum_eq_span {R S ι : Type*} [CommRing R] [AddCommGroup S] [Module R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) :
    Set.range (fun r : ι → R => ∑ i, r i • f i) = (Submodule.span R (Set.range f) : Set S) := by
  ext x
  rw [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]

end Commons.Algebra.Module
