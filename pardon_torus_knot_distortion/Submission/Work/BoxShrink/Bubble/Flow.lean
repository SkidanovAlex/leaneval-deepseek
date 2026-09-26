import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow

/-!
# The input from a periodic flow of the parameter plane

The geometric input of the chapter, `Work.BoxShrink.Bubble.SlicePushOff`, can also be phrased in
the *parameter plane* of the torus.  A continuous `Φ : ℝ → ℝ² → ℝ²` which is equivariant under the
period lattice `2πℤ²` (`hperiod`) descends to the surface and transport closed curves of `F` to
closed curves of `F` with the *same* winding vector
(`Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow`, the torus-generic form of
`Work.Smooth.Morse.Flow.exists_curve_periodicFlow`).  Consequently:

`Work.BoxShrink.Bubble.slicePushOff_of_planeFlow`:  if at time `1` the flow carries the preimage of
`boxRegion` into the preimage of `upperRegion ∪ lowerRegion` — i.e. in the surface, if it carries
`boxRegion` into `upperRegion ∪ lowerRegion` — then the input holds.

This is the form of the input which the smooth chapter can attack: for the surfaces
`P = ParamTorus.mapHomeomorph ψ.toHomeomorph` of the challenge, the pull-back
`G = pullback ψ (fun y => y (σ 2))` of the plane coordinate is smooth, and the flow of a
compactly supported, periodic vector field pointing into the side of the plane one wants to push to
(the gradient direction of `G`, damped near `∂PBox`) is the intended construction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The input from a periodic flow of the parameter plane.** -/
theorem slicePushOff_of_planeFlow {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (Φ : ℝ → ℝ × ℝ → ℝ × ℝ) (hcont : Continuous (Function.uncurry Φ))
    (hperiod : ∀ (r : ℝ) (q : ℝ × ℝ) (k l : ℤ),
      Φ r (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) =
        ((Φ r q).1 + k * (2 * Real.pi), (Φ r q).2 + l * (2 * Real.pi)))
    (hmaps : ∀ q : ℝ × ℝ, P.psi q.1 q.2 ∈ Work.BoxShrink.Core.boxRegion P s c σ →
      P.psi (Φ 1 q).1 (Φ 1 q).2 ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) :
    SlicePushOff P s c σ u := by
  intro k hk
  obtain ⟨γ, hγ, hkγ⟩ := hk
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  obtain ⟨γ', hγ'apply, hγ'wind⟩ := Flow.exists_curve_of_periodicFlow P Φ hcont hperiod L
  refine ⟨γ', fun t => ?_, ?_⟩
  · have hmem : P.psi (L.Θ t, L.Φ t).1 (L.Θ t, L.Φ t).2 ∈
        Work.BoxShrink.Core.boxRegion P s c σ := by
      show P.psi (L.Θ t) (L.Φ t) ∈ Work.BoxShrink.Core.boxRegion P s c σ
      rw [L.lifts t]
      exact hγ t
    rw [hγ'apply t]
    exact hmaps (L.Θ t, L.Φ t) hmem
  · rw [hγ'wind, ← Work.SurgeryInvariance.windingOf_eq P γ L, hkγ]

end

end Work.BoxShrink.Bubble
