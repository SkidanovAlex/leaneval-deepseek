import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 400000

/-- **Continuity of the angular slice of a trace-class datum on the closed interval
`[0, π/2]`.**

For `G` in the trace class (`TraceClass G`) and a positive radius `w > 0` the slice
`s ↦ G w s` is continuous on `Iθ = [0, π/2]`.  On the *open* interval `(0, π/2)` this is
`SmoothOpen G` restricted to the slice (`SmoothOpen.curry_θ`); at the two endpoints the
continuity within `[0, π/2]` is exactly the pair (endpoint *value*, one-sided *trace*) of
`TraceClass`: `G w 0 = 0` together with `G w s → 0` as `s → 0⁺`, and `G w (π/2) = 0`
together with `G w s → 0` as `s → (π/2)⁻`.  (`ContinuousWithinAt` on `Ioi 0` upgrades to
`Ici 0` by `continuousWithinAt_Ioi_iff_Ici`, and the closed interval `[0, π/2]` is a
subset of `Ici 0`; dually at `π/2`.) -/
theorem slice_continuousOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    ContinuousOn (fun s : ℝ => G w s) Work.Spaces.Iθ := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, -, -, -⟩ := hT
  show ContinuousOn (fun s : ℝ => G w s) (Set.Icc 0 (Real.pi / 2))
  -- the slice is continuous on the open interval, and its two one-sided endpoint
  -- limits vanish (the endpoint values are `0` by `TraceClass`)
  have hslice : ContinuousOn (fun θ : ℝ => G w θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hw).continuousOn
  have hL0 : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Ioi 0) 0 := by
    simpa only [ContinuousWithinAt, h0 w] using htr0 w hw
  have hLpi : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Iio (Real.pi / 2))
      (Real.pi / 2) := by
    simpa only [ContinuousWithinAt, hpi w] using htrpi w hw
  -- the two endpoints, now with the closed interval as the ambient set
  have hj0 : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Icc 0 (Real.pi / 2)) 0 := by
    have h1 : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Ici 0) 0 := by
      apply (continuousWithinAt_Ioi_iff_Ici (a := (0 : ℝ)) (f := fun s : ℝ => G w s)).1
      exact hL0
    exact h1.mono (fun x hx => hx.1)
  have hjpi : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Icc 0 (Real.pi / 2))
      (Real.pi / 2) := by
    have h1 : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Iic (Real.pi / 2))
        (Real.pi / 2) := by
      apply (continuousWithinAt_Iio_iff_Iic (a := Real.pi / 2) (f := fun s : ℝ => G w s)).1
      exact hLpi
    exact h1.mono (fun x hx => hx.2)
  intro θ hθ
  rcases lt_trichotomy θ 0 with h | h | h
  · exact absurd hθ.1 (not_le.mpr h)
  · subst h; exact hj0
  · rcases lt_trichotomy θ (Real.pi / 2) with h2 | h2 | h2
    · exact (hslice.continuousAt (isOpen_Ioo.mem_nhds ⟨h, h2⟩)).continuousWithinAt
    · subst h2; exact hjpi
    · exact absurd hθ.2 (not_le.mpr h2)

end Work.FTS.EllSol.EllPkgAux.MollDom
