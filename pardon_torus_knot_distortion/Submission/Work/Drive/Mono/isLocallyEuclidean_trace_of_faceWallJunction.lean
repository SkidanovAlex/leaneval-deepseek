import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.WallFaceJunction_holds

/-!
# The wall ∩ face junction: the requested form of the local model

This module proves `Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction` by reducing it to
the already proved local model `Work.Drive.Mono.WallFaceJunction_holds` of the sibling module.

The two statements have literally the same hypotheses *except* for the shape of the face
regularity: here it is stated with the sweep height of the linear functional `innerSL ℝ v`,

  `hregG : ∀ p, Pinch.par ψ p = z → fderiv ℝ (sweepHeight ψ (innerSL ℝ v)) p ≠ 0`,

whereas `WallFaceJunction_holds` uses the equivalent pullback form

  `fderiv ℝ (fun q => inner ℝ v (Pinch.par ψ q)) p ≠ 0`.

The bridge is `Work.Drive.EpsForm.sweepHeight_innerSL`, which says that the sweep height of
`innerSL ℝ v` **is** that pullback, so the two forms of `hregG` are inter-derivable by rewriting.
The conclusion `∃ O, IsOpen O ∧ z ∈ O ∧ IsLocallyEuclidean (O ∩ (carrier ∩ frontier …))` is
identical in the two statements.
-/

namespace Work.Drive.Mono

theorem isLocallyEuclidean_trace_of_faceWallJunction {ψ : Submission.Diffeo} {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ} {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hv : v ≠ 0) (hh : 0 < h) (hℓne : ℓ ≠ 0) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzb : z ∈ Submission.PBox s c σ)
    (hzface : inner ℝ v z = inner ℝ v c + u + h) (hzl : ℓ z = lam)
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)
    (hregG : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (innerSL ℝ v)) p ≠ 0)
    (hreg2 : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (innerSL ℝ v)) p) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  -- convert the two `hregG`/`hreg2` from the `sweepHeight ψ (innerSL ℝ v)` form to the pullback form
  refine Work.Drive.Mono.WallFaceJunction_holds hv hh hℓne hz hzb hzface hzl hreg ?_ ?_
  · intro p hp
    have h := hregG p hp
    rwa [Work.Drive.EpsForm.sweepHeight_innerSL ψ v] at h
  · intro p hp t
    have h := hreg2 p hp t
    rwa [Work.Drive.EpsForm.sweepHeight_innerSL ψ v] at h

end Work.Drive.Mono
