import Mathlib
import Submission.Work.Peluse.UControl.HistInv

/-!
# The phase-1 invariant is preserved by the phase-1 chain

`phase1Chain` iterates the PET step at the deterministic selection until the state is `Phase1Done`
or linear (see `HistReach2.lean`).  `phase1Chain_done` proves that a chain started in a `Phase1`
state ends in a `Phase1Done` state; this file proves the companion fact that the *whole* invariant
`Phase1` is still in force at the terminal state.

The argument is the same well-founded induction: at a stopped state either `Phase1Done` already
holds (and a stopped state is never linear by `Phase1.not_linear` for `d ≥ 2`), and at a
non-stopped state the step is `Phase1.step_sel` — legal because `Phase1.degree_sel_lt` supplies the
degree drop that a non-`Phase1Done` state guarantees.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-- **The phase-1 invariant at the end of the phase-1 chain.**  A chain started in a `Phase1`
state (with `d ≥ 2`) stays inside `Phase1`: the state reached by `phase1Chain` still satisfies
`Phase1` with the same constant `lc`. -/
theorem histPhase1Inv {d : ℕ} (hd2 : 2 ≤ d) (lc : ℤ) :
    ∀ X : HState d, Phase1 d X.1 lc X.2 → Phase1 d (phase1Chain X).1 lc (phase1Chain X).2 := by
  intro X
  induction X using WellFounded.induction (HState.rel_wf d) with
  | h X ih =>
    intro h
    rw [phase1Chain, WellFounded.fix_eq]
    by_cases hstop : X.2.IsLinearX ∨ Phase1Done X.2
    · rw [dif_pos hstop]
      rcases hstop with hl | hdone
      · exact absurd hl (Phase1.not_linear hd2 h)
      · exact h
    · rw [dif_neg hstop]
      refine ih (HState.step X (X.2.H_nonempty_of_not_linear (fun hl => hstop (Or.inl hl))))
        (X.2.weightH_step_sel_lt _) ?_
      exact Phase1.step_sel (by omega) h (fun hd => hstop (Or.inr hd))
        (X.2.H_nonempty_of_not_linear (fun hl => hstop (Or.inl hl)))

end

end Work.Peluse.UControl
