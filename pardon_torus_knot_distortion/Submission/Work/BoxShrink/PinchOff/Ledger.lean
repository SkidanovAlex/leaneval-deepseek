import Submission.Work.BoxShrink.ledger
import Submission.Work.BoxShrink.PinchOff.KeyRefuted

/-!
# The consequence of the refutation for the ledger

`Submission/Work/BoxShrink/ledger.lean` states the challenge's classical inputs as
`Work.BoxShrink.ClassicalInputs`, whose second field is the *disjunction*

  `Work.BoxShrink.BubbleDatum := Work.BoxShrink.Pinch.CountingHalf ∨ Work.BoxShrink.Pinch.SmoothHalfS`.

`KeyRefuted.lean` proves that the second disjunct — the abstract form of Pardon's Lemma 3 with only
the two endpoint hypotheses — is **false** (`not_smoothHalfS`).  Hence the disjunction is
*equivalent* to its first disjunct: the field has to be inhabited by the counting form
`Work.BoxShrink.Pinch.CountingHalf` (Pardon's Lemma 3 with the counting of his proof, which rules
out the tangency through his Lemma 2), or through a form carrying Pardon's perturbation argument
(his Lemma `doublebubble2`).

Nothing here changes the *proofs* of the ledger: every implication from `ClassicalInputs` to the
challenge remains valid; what changes is which of the two routes can possibly be completed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The ledger's `bubble` field is the counting form.**  The `SmoothHalfS` disjunct of
`Work.BoxShrink.BubbleDatum` is refuted, so the disjunction collapses to
`Work.BoxShrink.Pinch.CountingHalf`. -/
theorem bubbleDatum_iff_countingHalf :
    Work.BoxShrink.BubbleDatum ↔ Work.BoxShrink.Pinch.CountingHalf :=
  ⟨fun h => h.elim id (fun hS => absurd hS not_smoothHalfS), Or.inl⟩

/-- The ledger with its `bubble` field supplied by the counting form. -/
theorem classicalInputs_of_pushThrough_countingHalf
    (hp : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard)
    (hb : Work.BoxShrink.Pinch.CountingHalf) : Work.BoxShrink.ClassicalInputs :=
  ⟨hp, Or.inl hb⟩

/-- The ledger with its `bubble` field supplied by a proof of Pardon's *tamed* residual plus the
general position inputs — recorded for completeness, but see `not_forall_transverseSlice`: the
hypothesis `htrans` cannot be discharged for every configuration, so this is *not* a route to
`Work.BoxShrink.ClassicalInputs` as stated. -/
theorem classicalInputs_of_pushThrough_tame
    (hp : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard)
    (h : Work.BoxShrink.Pinch.PushOffHalfTame)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.ClassicalInputs :=
  ⟨hp, Or.inr (Work.BoxShrink.Pinch.smoothHalfS_of_pushOffHalfTame h htrans htame)⟩

end

end Work.BoxShrink.PinchOff
