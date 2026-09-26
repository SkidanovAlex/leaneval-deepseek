import Mathlib
import Submission.Work.Smooth.OneManifold.ae_isLocallyEuclidean_levelSet
import Submission.Work.BoxShrink.Pinch.PinchSweep

/-!
# The corrected form of `BoxSliceNice`

`Work.BoxShrink.Pinch.BoxSliceNice` asks, for *every* level `s`, `c`, `σ`, that the level set of the
level function `boxLevel s c σ = boxNorm c σ - s` of the box sphere be a *nice level*
(`Work.Smooth.Morse.NiceLevel`): a compact finite disjoint union of simple closed curves, bounding a
compact sublevel region.

That statement is ill-posed at a tangency level, where the trace of the box sphere on the surface
can be a finite set of points (e.g. a single point, at which the surface is tangent to the sphere);
such a trace is not a finite union of circles, and no local model can repair this.

The correct statement is the almost-everywhere one, which is what the box chapter proves for the
genericity of the vertex stratum: `ae_niceLevel`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **The level set of the box level function is the box-norm level set.** -/
theorem levelSet_boxLevel_eq (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.Smooth.Morse.levelSet ψ (Work.BoxShrink.Pinch.boxLevel s c σ) 0
      = Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s := by
  ext x
  rw [Work.Smooth.Morse.mem_levelSet, Work.Smooth.Morse.mem_levelSet]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, sub_eq_zero.mp h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, sub_eq_zero.mpr h⟩

/-- **Almost every box level is a nice level** — the corrected form of
`Work.BoxShrink.Pinch.BoxSliceNice`. -/
theorem ae_niceLevel {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hvert : Work.Smooth.BoxGeneric.AeNoVertex ψ c σ) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.boxLevel s c σ) 0 := by
  have hcirc := ae_isCircleUnion_levelSet (ψ := ψ) (c := c) (σ := σ) hvert
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hcirc, hne] with s hcircs _
  refine ⟨Work.Smooth.Morse.Surface.isCompact_levelSet ψ
      (Work.BoxShrink.Pinch.boxLevel_continuous s c σ) 0, ?_,
    Work.Smooth.Morse.Surface.isCompact_closedRegion ψ
      (Work.BoxShrink.Pinch.boxLevel_continuous s c σ) 0⟩
  rw [levelSet_boxLevel_eq ψ s c σ]
  exact hcircs

end

end Work.Smooth.OneManifold
