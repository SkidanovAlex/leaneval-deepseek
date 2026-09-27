import Mathlib
import Submission.Work.EKLC6Core.countable_dense_subgroup
import Submission.Work.EKLComp.X3Background

set_option linter.style.haveILetI false

namespace Work.EKLC6Core

/-- `X₃ = SL₃(ℝ)/SL₃(ℤ)` is second countable (a quotient of the second countable group `SL₃(ℝ)`
by an arbitrary subgroup), hence separable, hence -- being nonempty -- admits a sequence with
dense range. -/
theorem exists_dense_seq_X3 : ∃ y : ℕ → Work.EKLContract.X3, Dense (Set.range y) := by
  haveI : SecondCountableTopology Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.1
  haveI : Nonempty Work.EKLContract.X3 := inferInstance
  obtain ⟨y, hy⟩ := TopologicalSpace.exists_dense_seq Work.EKLContract.X3
  exact ⟨y, hy⟩

end Work.EKLC6Core
