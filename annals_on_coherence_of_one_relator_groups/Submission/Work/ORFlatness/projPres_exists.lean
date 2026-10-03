import Mathlib
import Submission.Work.ORFlatness.Flat

namespace Work.ORFlatness

universe u

open TensorProduct MulOpposite

/-- Every right `R`-module has a projective presentation (`Work.ORFlatness.ProjPres`,
defined in `Submission.Work.ORFlatness.Flat`): the free right `R`-module on the
underlying type of `X` maps onto `X`.  Concretely `P := X →₀ Rᵐᵒᵖ` with covering map
`Finsupp.linearCombination Rᵐᵒᵖ (fun x => x)`, which is surjective since `x` is the image
of `Finsupp.single x 1`; `P` is free by `Module.Free.finsupp` and hence projective by
`Module.Projective.of_free`. -/
theorem projPres_exists {R : Type u} [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] : Nonempty (Work.ORFlatness.ProjPres R X) := by
  refine ⟨{ P := X →₀ Rᵐᵒᵖ, π := Finsupp.linearCombination Rᵐᵒᵖ (fun x => x),
            surj := ?_ }⟩
  intro x
  exact ⟨Finsupp.single x 1, by rw [Finsupp.linearCombination_single]; simp⟩

end Work.ORFlatness
