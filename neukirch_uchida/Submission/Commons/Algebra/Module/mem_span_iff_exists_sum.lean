import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Submission.Commons.Algebra.Module.range_sum_eq_span

namespace Commons.Algebra.Module

lemma mem_span_iff_exists_sum {R S ι : Type*} [CommRing R] [AddCommGroup S] [Module R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) (x : S) :
    x ∈ Submodule.span R (Set.range f) ↔ ∃ r : ι → R, x = ∑ i, r i • f i := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr fun r => eq_comm

end Commons.Algebra.Module