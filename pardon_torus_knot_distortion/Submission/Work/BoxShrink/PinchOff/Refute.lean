import Submission.Work.BoxShrink.PinchOff.Discs
import Submission.Work.BoxShrink.Bubble.Refutation

/-!
# The transport form is false (in Lean)

The chapter's residual is the *one-sided dimension bound* `Key`, not the loop transport
`Transport`.  This module records the refutation in this chapter's vocabulary: the parent chapter's
`Work.BoxShrink.Bubble.standard_counterexample` exhibits a configuration of the standard torus
(`s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0`) in which **both** endpoint hypotheses hold -- the box
sphere and the slice carry no essential loop -- and the loop transport fails.  Hence `Transport` is
false, and with it the strong (span) form `Strong` *as a universally quantified statement over
configurations with `hS` and `hZ`*: what survives is exactly `Key`.

The numerical study in `Submission/Work/BoxShrink/Pinch/EXP` sharpens the point: the transport form
stays false even after adding the hypothesis that the trace of the *plane* is inessential
(`spanbot.py`), so no restriction of the transport form along those lines can be the residual.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The transport form is false.**  At the standard torus with the box `s = 5/2` cut by the plane
`{y = 0}` (`σ = swap 1 2`, `u = 0`), both the sphere trace and the slice carry no essential loop,
yet the region inside the box is not loop-equivalent to the two half-regions
(`Work.BoxShrink.Bubble.standard_counterexample`). -/
theorem not_transport : ¬ Transport := by
  intro h
  obtain ⟨hS, hZ, hnot⟩ := Work.BoxShrink.Bubble.standard_counterexample
  have h1 : surface Work.BoxShrink.Bubble.idDiffeo = Work.CoreTopology.standard :=
    Work.BoxShrink.Bubble.mapHomeomorph_idDiffeo_eq_standard
  have hS' : ¬ (surface Work.BoxShrink.Bubble.idDiffeo).ContainsEssentialLoop
      (SphereTrace (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2)) := by
    rw [h1]; exact hS
  have hZ' : ¬ (surface Work.BoxShrink.Bubble.idDiffeo).ContainsEssentialLoop
      (Sigma Work.BoxShrink.Bubble.idDiffeo (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0) := by
    rw [h1]; exact hZ
  have hRE := h Work.BoxShrink.Bubble.idDiffeo (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 hS' hZ'
  exact hnot ((Work.BoxShrink.Pinch.regionTransport_iff_slicePushOff
    (P := surface Work.BoxShrink.Bubble.idDiffeo) (s := (5 / 2 : ℝ)) (c := 0)
    (σ := Equiv.swap (1 : Fin 3) 2) (u := 0)).mp hRE)

/-- **The hypothesis `hS` of the residual is not redundant.**  At the configuration of the standard
small box (`s = 3/2`, `σ = swap 1 2`, `u = 0`) at which Pardon's Lemma 3 conclusion *fails*
(`Work.BoxShrink.Pinch.BubbleHalfRefuted`), the trace of the box sphere *is* essential
(`Work.BoxShrink.Pinch.sphereSet_threeHalves_essential`): the interface of `Key` -- which carries
`hS` -- is not touched by that refutation. -/
theorem sphereTrace_essential_of_refuted_config :
    (surface Work.BoxShrink.Bubble.idDiffeo).ContainsEssentialLoop
      (SphereTrace (3 / 2) 0 (Equiv.swap (1 : Fin 3) 2)) := by
  have h1 : surface Work.BoxShrink.Bubble.idDiffeo = Work.CoreTopology.standard :=
    Work.BoxShrink.Bubble.mapHomeomorph_idDiffeo_eq_standard
  rw [h1]
  exact Work.BoxShrink.Pinch.sphereSet_threeHalves_essential

end

end Work.BoxShrink.PinchOff
