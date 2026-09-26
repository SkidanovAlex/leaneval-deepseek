import Submission.Work.BoxShrink.PinchOff.Tamed
import Submission.Work.BoxShrink.PinchOff.tangent_not_transverseSlice

/-!
# The general position hypotheses are not free

`KeyRefuted.lean` shows that the *abstract* residual of the pinch (`Key`, `SmoothHalfS`,
`PardonPinchInput`, all the forms without a general position hypothesis) is false, and that the
missing hypothesis is the transversality of the cutting plane.  The corrected residual
`SmoothHalfSTame` / `Work.BoxShrink.Pinch.PushOffHalfTame` (`Tamed.lean`) carries exactly that
hypothesis — and this module records the matching *negative* fact: the hypothesis cannot be dropped
either, since it is not available for every configuration.

* `tangent_not_transverseSlice` (delegated, axiom-clean, in
  `Submission.Work.BoxShrink.PinchOff.tangent_not_transverseSlice`) — the cutting plane of the
  tangent configuration is not transverse at its tangency point;
* `not_forall_transverseSlice` — consequently neither `TransverseSlice` nor `TransverseTrace` holds
  for every smooth configuration, so the parent chapter's `smoothHalfS_of_pushOffHalfTame` cannot be
  applied globally, and the abstract field `Work.BoxShrink.Pinch.SmoothHalfS` of the ledger's
  `bubble` must not be used.  The surviving route to the ledger's second field is the *counting*
  form `Work.BoxShrink.Pinch.CountingHalf` (Pardon's Lemma 3 with the counting of his proof), or a
  form carrying Pardon's perturbation argument (his Lemma `doublebubble2`, whose conclusion is
  invariant under arbitrarily small perturbations of the double bubble and therefore does not
  require the transversality of the *given* box/plane configuration).

The lesson: the pinch residual is a *conditional* statement about configurations in general
position, and every unconditional form of it is false.  This is exactly what Pardon's paper does —
he puts the double bubble in general position (a perturbation, Lemma `doublebubble2`) before
applying Lemma `doublebubble` — and what the counting hypothesis supplies in the crux.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **Transversality of the cutting plane is not a theorem about all configurations**: the tangent
configuration of the standard torus violates it. -/
theorem not_forall_transverseSlice :
    ¬ (∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :=
  fun h => tangent_not_transverseSlice (h idDiffeo tangentRad tangentCtr tangentCyc3 0)

/-- **Transversality of the cutting plane along the whole trace fails at the tangent
configuration** (the trace of the plane is global, so this is the form the parent chapter's
`TraceLineSmooth` and the loop-transport statements carry). -/
theorem tangent_not_transverseTrace :
    ¬ Work.BoxShrink.Pinch.TransverseTrace idDiffeo tangentCtr tangentCyc3 0 :=
  fun h => tangent_not_transverseSlice
    (Work.BoxShrink.Pinch.transverseSlice_of_transverseTrace tangentRad h)

/-- Consequently the *global* form of the transversality hypothesis is false as well. -/
theorem not_forall_transverseTrace :
    ¬ (∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseTrace ψ c σ u) :=
  fun h => tangent_not_transverseTrace (h idDiffeo tangentCtr tangentCyc3 0)

end

end Work.BoxShrink.PinchOff
