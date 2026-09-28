import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polar_basic
import Submission.Work.HP.MDEstimates.polarQuadFacts
import Submission.Work.HP.Q44Main.QuadCount.polarLMHalfHess
import Submission.Work.HP.Q44Main.QuadCount.polQSingleHalfHess
import Submission.Work.HP.Q44Main.QuadCount.polQExpand

namespace Work.HP.Q44Main.QuadCount

open MvPolynomial

/-- The radical of the polar form, cut out by the coefficient matrix `polarLM`, agrees with the
set of vectors pairing trivially with every vector under the polar form `polQ`. -/
theorem radSub_mem_iff (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (v : Fin 5 → ℚ) :
    v ∈ Work.HP.MDEstimates.radSub Q ↔ v ∈ Work.HP.MDEstimates.radQ Q := by
  change Work.HP.MDEstimates.polarLM Q v = 0 ↔
    ∀ w : Fin 5 → ℚ, Work.HP.MDEstimates.polQ Q v w = 0
  have key : ∀ i : Fin 5, Work.HP.MDEstimates.polQ Q v (Pi.single i 1)
      = (Work.HP.MDEstimates.polarLM Q v) i := fun i => by
    rw [polQSingleHalfHess Q hQ v i, polarLMHalfHess Q v i]
  constructor
  · intro h w
    rw [polQExpand Q hQ v w]
    apply Finset.sum_eq_zero
    intro i _
    rw [key i, congrFun h i]
    simp
  · intro h
    funext i
    rw [Pi.zero_apply, ← key i]
    exact h (Pi.single i 1)

end Work.HP.Q44Main.QuadCount
