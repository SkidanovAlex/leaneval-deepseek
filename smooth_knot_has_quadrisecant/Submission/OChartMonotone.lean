import Mathlib
import Submission.OSubChart
import Submission.Commons.Topology.Order.strictMonoOn_or_strictAntiOn_of_continuousOn_injOn

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **Injective continuous real maps on an open interval are strictly
monotone.**  An injective continuous map from an open real interval (as a
`ChartInterval` subtype) into `ℝ` is either strictly order-preserving or
strictly order-reversing: read it through its extension to the real line
and apply the commons L28
(`Commons.Topology.Order.strictMonoOn_or_strictAntiOn_of_continuousOn_injOn`)
to the preconnected open interval.  This is the monotone-coordinate engine
of the chain gluing: transition maps between interval pieces need not be
onto, so only injectivity and continuity are required. -/
theorem interval_inj_continuous_monotone {lo hi : ℝ}
    (f : ChartInterval lo hi → ℝ) (hfcont : Continuous f)
    (hfinj : Function.Injective f) :
    (∀ x y : ChartInterval lo hi, (x : ℝ) < (y : ℝ) → f x < f y) ∨
    (∀ x y : ChartInterval lo hi, (x : ℝ) < (y : ℝ) → f y < f x) := by
  let F : ℝ → ℝ := fun z => if hz : z ∈ Set.Ioo lo hi then f ⟨z, hz⟩ else 0
  have F_val : ∀ {z : ℝ} (hz : z ∈ Set.Ioo lo hi), F z = f ⟨z, hz⟩ := by
    intro z hz
    change (if h : z ∈ Set.Ioo lo hi then f ⟨z, h⟩ else 0) = f ⟨z, hz⟩
    rw [dif_pos hz]
  have hs : IsPreconnected (Set.Ioo lo hi : Set ℝ) := isPreconnected_Ioo
  have hcont : ContinuousOn F (Set.Ioo lo hi : Set ℝ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (Set.Ioo lo hi : Set ℝ).domRestrict F =
        (fun a : {a : ℝ // a ∈ Set.Ioo lo hi} => f a) := by
      funext a
      change F (a : ℝ) = f a
      rw [F_val a.2]
    rw [hfun]
    exact hfcont
  have hinj : Set.InjOn F (Set.Ioo lo hi : Set ℝ) := by
    intro z₁ hz₁ z₂ hz₂ hF
    have h1 : f (⟨z₁, hz₁⟩ : ChartInterval lo hi) = f (⟨z₂, hz₂⟩ : ChartInterval lo hi) := by
      rw [← F_val hz₁, ← F_val hz₂]
      exact hF
    have hz : (⟨z₁, hz₁⟩ : ChartInterval lo hi) = (⟨z₂, hz₂⟩ : ChartInterval lo hi) := hfinj h1
    exact congrArg Subtype.val hz
  rcases Commons.Topology.Order.strictMonoOn_or_strictAntiOn_of_continuousOn_injOn hs hcont hinj with
    hmono | hanti
  · left
    intro x y hxy
    have hFxy : F (x : ℝ) < F (y : ℝ) := hmono x.2 y.2 hxy
    rw [F_val x.2, F_val y.2] at hFxy
    simpa using hFxy
  · right
    intro x y hxy
    have hFyx : F (y : ℝ) < F (x : ℝ) := hanti x.2 y.2 hxy
    rw [F_val y.2, F_val x.2] at hFyx
    simpa using hFyx

/-- **Open-interval homeomorphisms are strictly monotone** (corollary of the
injective-continuous engine: an open-interval homeo read through its real
values is injective continuous). -/
theorem homeoChartInterval_monotone {lo₁ hi₁ lo₂ hi₂ : ℝ}
    (e : ChartInterval lo₁ hi₁ ≃ₜ ChartInterval lo₂ hi₂) :
    (∀ x y : ChartInterval lo₁ hi₁, (x : ℝ) < (y : ℝ) → (e x : ℝ) < (e y : ℝ)) ∨
    (∀ x y : ChartInterval lo₁ hi₁, (x : ℝ) < (y : ℝ) → (e y : ℝ) < (e x : ℝ)) := by
  let f : ChartInterval lo₁ hi₁ → ℝ := fun x => ((e x : ChartInterval lo₂ hi₂) : ℝ)
  have hfcont : Continuous f := continuous_subtype_val.comp e.continuous
  have hfinj : Function.Injective f := by
    intro x y h
    have hxy : e x = e y := by
      apply Subtype.ext
      exact h
    exact e.injective hxy
  rcases interval_inj_continuous_monotone f hfcont hfinj with hmono | hanti
  · left
    intro x y hxy
    exact hmono x y hxy
  · right
    intro x y hxy
    exact hanti x y hxy

/-- The coordinate relabelling of a chart cell preserves the real
parameter exactly (it is the identity on the underlying real numbers), so
it is trivially order-preserving. -/
lemma cellIntervalHomeo_preserves_param {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) {lo hi : ℝ} (hlo : c.lo < lo) (hhi : hi < c.hi)
    (x : ChartInterval lo hi) :
    (((cellIntervalHomeo c hlo hhi x : {x : ChartInterval c.lo c.hi // (x : ℝ) ∈ Set.Ioo lo hi}) :
        ChartInterval c.lo c.hi) : ℝ) = (x : ℝ) := by
  rfl

end LeanEval.KnotTheory.Quadrisecant
