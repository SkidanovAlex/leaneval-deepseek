import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Cover

/-- Second countability is a countable-local property: if a space is covered by countably many
open subspaces each of which is second countable, then so is the space itself.  (No monotonicity
of the cover is needed; the name records the use in Brown's monotone-union argument.) -/
theorem secondCountableTopology_of_monotone_open_cover {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hopen : ∀ k, IsOpen (U k)) (hcover : (⋃ k, U k) = Set.univ)
    (hsc : ∀ k, SecondCountableTopology ↥(U k)) : SecondCountableTopology X :=
  @TopologicalSpace.secondCountableTopology_of_countable_cover X _ ℕ _ U hsc hopen hcover

end Work.Brown.Cover
