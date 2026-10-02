import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup

/-!
# The "meeting edges" of an edge, for the second family round

`meetSet 𝓖 e` is the set of edges of `𝓖` other than `e` which meet `e`.  It is the
combinatorial quantity that controls the mean of `badSum` in `r2_Wfam_mean`: a kept
edge `e` is *bad* exactly when some edge of `meetSet 𝓖 e` is also kept, and by the
union bound the probability of this is at most `|meetSet 𝓖 e| · p²`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped BigOperators

namespace Work.Deep.Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `𝓖` other than `e` which meet `e`. -/
noncomputable def meetSet (𝓖 : Set (Set V)) (e : 𝓖) : Finset 𝓖 := by
  classical
  exact Finset.univ.filter (fun f : 𝓖 => f ≠ e ∧ ((f : Set V) ∩ (e : Set V)).Nonempty)

@[simp] lemma mem_meetSet {𝓖 : Set (Set V)} {e f : 𝓖} :
    f ∈ meetSet 𝓖 e ↔ f ≠ e ∧ ((f : Set V) ∩ (e : Set V)).Nonempty := by
  classical simp [meetSet]

end Work.Deep.Nibble
