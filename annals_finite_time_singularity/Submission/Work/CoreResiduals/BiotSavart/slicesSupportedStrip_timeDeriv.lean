import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.StabilityFar.Decay.slicesSupported_timeDeriv_window

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The `∂ₜ`-slices of a bundled strip vorticity are supported in the support ball.**

Let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S` (its slices are supported in
`closedBall 0 R`) and let `0 < S`.  Then for every `t ∈ Icc 0 S` the slice `y ↦ ∂ₜω(y,t)` is
supported in `closedBall 0 R`.

**Proof sketch.**  For `R < ‖y‖`, the slice `ω(y,·)` vanishes on all of `Icc 0 S` (support clause),
so for `t ∈ Ioo 0 S` the derivative `∂ₜω(y,t)` vanishes by the two-sided argument of
`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall`.  At the endpoint `t = 0` the
bundle's `HasDerivAt (fun s => ω y s) (∂ₜω y 0) 0` (a *two-sided* derivative) restricts to
`HasDerivWithinAt` on `Ioi 0`, where the function is *identically* `0` near `0` (on `(0,S)`, using
the support clause), so `0` is also a derivative there; uniqueness of the derivative within `Ioi 0`
at `0` (`UniqueDiffWithinAt ℝ (Ioi 0) 0`) gives `∂ₜω(y,0) = 0`.  Similarly at `t = S`.

**Note.**  The hypothesis `0 < S` cannot be dropped: for `S = 0` the bundle constrains the slices
only at the single time `0`, so `∂ₜω(·,0)` (the two-sided derivative) may be supported anywhere
(`ω y s := s • c y` satisfies the whole bundle and `∂ₜω y 0 = c y`).  Same caveat as
`Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle`. -/
theorem slicesSupportedStrip_timeDeriv {α : NNReal} {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {R S : ℝ} (hS : 0 < S) (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      FiniteTimeSingularity.timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
  -- Extract the support clause of the strip bundle.
  have hsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := hbun.1.2.1
  intro t ht y hy
  by_contra hmem
  -- Off the support ball the slice `s ↦ ω y s` vanishes on the whole strip.
  have hvan : ∀ s ∈ Set.Icc (0:ℝ) S, ω y s = 0 := by
    intro s hs
    by_contra hne
    exact hmem (hsupp s hs y hne)
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · -- Interior / left of the right endpoint: `ω y` vanishes on `[t, t + (S-t))`.
    refine hy (Work.StabilityFar.timeDeriv_eq_zero_of_eq_zero_on_Ico (ω := ω) (x := y)
      (t := t) (ε := S - t) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩
  · -- Right endpoint `t = S`: `ω y` vanishes on `(S - S, S]`.
    rw [heq] at hy
    refine hy (Work.StabilityFar.timeDeriv_eq_zero_of_eq_zero_on_Ioc (ω := ω) (x := y)
      (t := S) (ε := S) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1], by linarith [hs.2]⟩

end Work.CoreResiduals.BiotSavart
