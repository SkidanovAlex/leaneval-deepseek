import Mathlib.Data.Set.Card.Arithmetic

set_option linter.unusedVariables false

namespace Commons.Combinatorics.Set

/-- The number of elements covered by a finite union of finite sets is at most the
sum of the cardinalities of the sets. -/
theorem ncard_biUnion_le {α ι : Type*} (t : Finset ι) (S : ι → Set α)
    (hfin : ∀ i ∈ t, (S i).Finite) :
    (⋃ i ∈ t, S i).ncard ≤ ∑ i ∈ t, (S i).ncard :=
  Finset.set_ncard_biUnion_le t S

end Commons.Combinatorics.Set