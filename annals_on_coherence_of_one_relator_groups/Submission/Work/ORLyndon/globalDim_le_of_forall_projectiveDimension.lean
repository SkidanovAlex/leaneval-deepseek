import Mathlib
import Submission.Work.ORCoherence.GlobalDim

namespace Work.ORLyndon

universe u

/-- If every left `R`-module has projective dimension at most `n`, then the global dimension of
`R` is at most `n`.  This is the easy direction of `Work.ORCoherence.GlobalDim.globalDim_le_iff`:
the global dimension is the supremum of the projective dimensions of the left `R`-modules, so it
suffices to bound each term in the supremum, using
`CategoryTheory.projectiveDimension_le_iff`. -/
theorem globalDim_le_of_forall_projectiveDimension {R : Type u} [Ring R] {n : ℕ}
    (h : ∀ (M : ModuleCat.{u} R), CategoryTheory.HasProjectiveDimensionLE M n) :
    Work.ORCoherence.globalDim R ≤ (n : WithBot ℕ∞) := by
  rw [Work.ORCoherence.globalDim, iSup_le_iff]
  intro M
  exact (CategoryTheory.projectiveDimension_le_iff M n).mpr (h M)

end Work.ORLyndon
