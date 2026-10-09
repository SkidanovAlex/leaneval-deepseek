import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Algebra.Module

lemma range_sum_eq_span {R S ι : Type*} [CommRing R] [AddCommGroup S] [Module R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) :
    Set.range (fun r : ι → R => ∑ i, r i • f i) = (Submodule.span R (Set.range f) : Set S) := by
  ext x
  rw [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]

end Commons.Algebra.Module
