import Mathlib

namespace Work.EQ

/-- In a second-countable space, an uncountable set has an accumulation point lying in it.

Proof: if no point of `s` is an accumulation point of `s`, then `s` carries the discrete
topology (`discreteTopology_of_noAccPts`), hence its inclusion into `X` is such that every
point is isolated; a second-countable space is hereditarily Lindelöf, so a discrete subset of
it is countable (`IsLindelof.countable`). This contradicts `¬ s.Countable`. -/
theorem exists_accPt_principal_of_uncountable {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {s : Set X} (hs : ¬ s.Countable) :
    ∃ x ∈ s, AccPt x (Filter.principal s) := by
  by_contra h
  simp only [not_exists, not_and] at h
  have hd : DiscreteTopology s := discreteTopology_of_noAccPts h
  exact hs ((HereditarilyLindelofSpace.isLindelof s).countable hd)

end Work.EQ
