/-
# `Work.SolutionDelivery.BiotSavartTime` — `∂ₜu = BS(∂ₜω)` is *derived*, not assumed

`Work.StabilityFar.AssemblyInputs.bsTimeSlice` — the identity `∂ₜu(·,t) = BS(∂ₜω(·,t))` — is one
of the two Biot–Savart dictionary clauses of the assembly.  `NOTES.md` of `Work.StabilityFar` (§6
item 3) records it as removable: the pointwise differentiation under the Biot–Savart integral is
*proved* there (`Work.StabilityFar.Decay.hasDerivAt_biotSavart`), and only the conversion into a
slicewise identity was left open.  This module performs the conversion: from

* the Biot–Savart reconstruction `u(x,t) = BS(ω(·,t)) x` on the *open* extended window (a genuine
  two-sided neighbourhood of every point of `window T = [-1,T+1]` — this is why the reconstruction
  is imposed there rather than on the closed window), and
* the differentiability of the slices `s ↦ ω(y,s)`, their measurability, the support radius `R`
  and the bounds `M`, `M₁`,

one gets `Work.StabilityFar.IsTimeBiotSavartSlice u ω T`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The time-slice of the Biot–Savart dictionary, derived from the pointwise one.**

If `u(x,s) = BS(ω(·,s)) x` on the open extended window `extWindow T = (-2,T+2)`, and if the slices
`s ↦ ω(y,s)` are differentiable (with derivative `∂ₜω`), measurable, supported in `B(0,R)` and
bounded by `M`, `M₁` there, then `∂ₜu(·,t) = BS(∂ₜω(·,t))` on the physical window
`window T = [-1,T+1]`. -/
theorem isTimeBiotSavartSlice_of_extSlice {u ω : R3 → ℝ → R3} {R M M₁ T : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁)
    (hbs : ∀ t ∈ extWindow T, ∀ x : R3,
      u x t = Work.LWP.biotSavart (fun y => ω y t) x)
    (hdc : ∀ t ∈ extWindow T, ∀ y : R3,
      HasDerivAt (fun s => ω y s) (timeDeriv ω y t) t)
    (hbdd : ∀ t ∈ extWindow T, ∀ y : R3, ‖ω y t‖ ≤ M)
    (hbddDt : ∀ t ∈ extWindow T, ∀ y : R3, ‖timeDeriv ω y t‖ ≤ M₁)
    (hsupp : ∀ t ∈ extWindow T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : ∀ t ∈ extWindow T, MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume) :
    Work.StabilityFar.IsTimeBiotSavartSlice u ω T := by
  intro t ht x
  have hmem : t ∈ extWindow T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- a two-sided neighbourhood of `t` contained in the extended window
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extWindow T).mem_nhds hmem)
  have hε : 0 < ε := hεpos
  -- the neighbourhood, in the `Ioo` form used by `hasDerivAt_biotSavart`
  have hnear : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ extWindow T := by
    intro s hs
    exact hεsub (Metric.mem_ball.mpr (by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩))
  -- differentiation under the Biot–Savart integral
  have hderiv : HasDerivAt (fun s => Work.LWP.biotSavart (fun y => ω y s) x)
      (Work.LWP.biotSavart (fun y => timeDeriv ω y t) x) t :=
    Work.StabilityFar.Decay.hasDerivAt_biotSavart hR hM hM₁ hε
      (fun s hs y => hbdd s (hnear s hs) y)
      (fun s hs y => hbddDt s (hnear s hs) y)
      (fun s hs y => hdc s (hnear s hs) y)
      (fun s hs y => hsupp s (hnear s hs) y)
      (fun s hs => hmeas s (hnear s hs)) x
  -- the two functions agree near `t`
  have heq : (fun s => u x s) =ᶠ[𝓝 t]
      (fun s => Work.LWP.biotSavart (fun y => ω y s) x) := by
    filter_upwards [(isOpen_extWindow T).mem_nhds hmem] with s hs
    exact hbs s hs x
  rw [timeDeriv, heq.deriv_eq]
  exact hderiv.deriv

end Work.SolutionDelivery
