import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths
import Submission.Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_square_boundary_subset_of_isCompact_isUnbounded_component
import Submission.Work.RPB.B1a.Maehara.Core
import Submission.Work.RPB.B1a.Maehara.exists_bounded_component_complex_of_normalized

namespace Work.RPB.B1a

/-- **The complement of a Jordan curve in the plane has a bounded connected component.**

A continuous injective map of the circle into the plane has an image whose complement contains a
point whose connected component is bounded (the "interior" of the Jordan curve).  The proof is
Maehara's: one transports the statement to the complex plane, normalises the curve by a similarity
so that it lies in `[-1,1] × [-2,2]` and meets the boundary of that rectangle only in `-1` and `1`,
and then runs the rectangle argument
(`Work.RPB.B1a.maehara_normalized`, see `Submission.Work.RPB.B1a.Maehara.Core`). -/
theorem exists_bounded_component_compl (γ : Circle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ) :
    ∃ x : ℝ × ℝ, x ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x) := by
  rw [Work.RPB1a.Caratheodory.Brouwer.cpx_transport_bounded_component γ]
  refine Work.RPB.B1a.Maehara.exists_bounded_component_complex_of_normalized ?_ _ ?_ ?_
  · intro γ' hγ' hinj' hm1 h1 hsub hbd
    exact maehara_normalized γ' hγ' hinj' hm1 h1 hsub hbd
  · exact Complex.equivRealProdCLM.symm.continuous.comp hγ
  · exact fun a b hab => hinj (Complex.equivRealProdCLM.symm.injective hab)

end Work.RPB.B1a
