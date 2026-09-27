import Mathlib
import Submission.Work.Cohomology.Pairing
import Submission.Work.Cohomology.exists_chain_eval_ne_zero

namespace Work.Pairing

/--
The evaluation pairing of a rational cohomology class with cycles is injective: over the field
`ℚ` a cohomology class is determined by its values on cycles (the easy half of the universal
coefficient theorem).  If the class of a cocycle `u` vanishes on all cycles, then `u` vanishes on
all cycles, hence is a coboundary by `Work.Cohomology.exists_chain_eval_ne_zero`, so its class
is zero.
-/
theorem pairMap_injective (S : SSet.{0}) (n : ℕ) :
    Function.Injective (Submission.Cohomology.pairMap S n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
      obtain ⟨u, hu⟩ := u
      rw [show (Submodule.Quotient.mk ⟨u, hu⟩ : Submission.Cohomology.H S ℚ n)
            = Submission.Cohomology.H.mk u hu from rfl] at hx ⊢
      by_contra hne
      obtain ⟨c, hc, hcv⟩ := Work.Cohomology.exists_chain_eval_ne_zero u hu hne
      have h0 : Submission.Cohomology.pairMap S n (Submission.Cohomology.H.mk u hu)
          ⟨c, hc⟩ = 0 := by
        rw [hx]; rfl
      rw [Submission.Cohomology.pairMap_mk] at h0
      exact hcv h0

end Work.Pairing
