import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.Band.BandChartDefs

/-!
# Non-degenerate events, and the bad set of "one event per level" (route I, reformulated)

Project lead, `Submission/Work/Drive/Mono/NOTES_LEAD_LD_interface.md` §0.1 and §4: every refutation of
the earlier spellings of "one event per level" (a flat patch of the surface in a box face, a straight
segment of the surface parallel to the sweep direction, a wavy torus with two critical circles on one
level) used a **degenerate** event.  The reformulation puts pointwise **non-degeneracy inside the bad
set** and varies the cutting level `u` together with `(h, τ)`; the resulting statement needs no
`BoxGen`, no `GammaTransverse` and no `TiltedGenericity` hypothesis.

`Work.Drive.Mono.NDEvent` is the non-degeneracy predicate, one clause per event type
(`Work.Drive.Final.IsEvent`, `IsFaceEvent`, `IsCornerEvent`); `Work.Drive.Mono.OneEvBad` is the bad
set: two *distinct* non-degenerate events of the swept level `ℓ_τ` with the same level, not both
critical points.

The producers of the two nullity statements are `Work.Drive.Mono.oneEvBad_null3` (the `ℝ³`-form) and
`Work.Drive.Mono.ae_oneEvBad_slice_null` (the a.e.-`u` slice form).
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal RealInnerProductSpace

namespace Work.Drive.Mono

noncomputable section

/-- **A non-degenerate event of the tilted sweep**, one clause per event type:

* `IsEvent` (a critical point of the sweep height in the box and the closed slab): the level is
  *strictly* inside the slab (`|slabFn| < h`) and the Hessian of the sweep height at the point is
  injective (a non-degenerate critical point);
* `IsFaceEvent` (a tangency of the level with a slab face inside the box): the sweep height and the
  slab height are both submersions there, and the constrained second derivative of
  `sweepHeight - t·slabFnPar` is nonzero on the face-tangent direction;
* `IsCornerEvent` (a point of the surface on the box sphere and on a slab face): exactly one active
  vertical face `i ≠ 2` (the others strictly inside the box), the pair
  `q ↦ ((par q) (σ i), ⟪v, par q⟫)` has invertible derivative there, and the level is not tangent to
  that face. -/
def NDEvent (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  (Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p ∧
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| < h ∧
      Function.Injective (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p)) ∨
  (Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
      fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p →
        ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p w = 0 →
          (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
            Work.Drive.EpsForm.sweepHeight ψ ℓ q
              - t * Work.Drive.Final.slabFnPar ψ c u v q)) p) w w ≠ 0) ∨
  (Work.Drive.Final.IsCornerEvent ψ s c σ u v h p ∧
      ∃ i : Fin 3, i ≠ 2 ∧
        (∀ j : Fin 3, j ≠ i →
          |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| < Submission.boxSide j * s) ∧
        (fderiv ℝ (fun q : ℝ × ℝ =>
          ((Work.BoxShrink.Pinch.par ψ q) (σ i), inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) p).IsInvertible ∧
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p)

/-- **The bad set of "one event per level"**: there are two *distinct* non-degenerate events of the
swept level `ℓ_τ` with the same level, and not both of them are critical points (pairs of two critical
points with equal value are excluded by clause (iv) of `Work.Drive.Final.TiltedGenericity` at the
datum).  Here `u` is the cutting level, `h` the half-width of the slab and `τ` the tilt parameter of
the family `ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫`. -/
def OneEvBad (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (a₀ b₀ : R3) (u h τ : ℝ) : Prop :=
  ∃ p p' : ℝ × ℝ,
    NDEvent ψ s c σ u v h ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p ∧
    NDEvent ψ s c σ u v h ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p' ∧
    (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (Work.BoxShrink.Pinch.par ψ p) =
      (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (Work.BoxShrink.Pinch.par ψ p') ∧
    Work.BoxShrink.Pinch.par ψ p ≠ Work.BoxShrink.Pinch.par ψ p' ∧
    ¬ (Work.Drive.Final.IsEvent ψ s c σ u v h
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p ∧
       Work.Drive.Final.IsEvent ψ s c σ u v h
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p')

end

end Work.Drive.Mono
