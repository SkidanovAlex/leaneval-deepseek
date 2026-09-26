/-
# The identity theorem on the chart ball: comparing two charts

Every chart of the CKMRV layer continuation (`Work.LayerCont.layerWindowContinuation`,
`..._rev`, `..._one`, `Work.LayerCont.layerTruncContinuation`) is a holomorphic function on a
hyperbolic ball `B(1 + i s₀, ε')` agreeing with the paper's layer `paperLayer` on the `𝒟`-side of
that ball.  Two such charts with the same centre are therefore *the same function* on the smaller
of their two balls: their difference is holomorphic and vanishes on the non-empty open subset where
both equal `paperLayer`.

This file records that step.  It is what turns the *one* far-side computation of
`Work.LayerCont.FarTail.far_identity` (the window chart, `Re τ > 1`) into the far-side statement
for every other chart at the same height: on the far side a chart is
`paperLayer (Gcusp ℓ d) ℓ d · r + sinSqC r · resCorr r ·`, with the *same* residue correction.

The analytic input is the standard identity theorem along the hyperbolic ball.  The ball
`B(c,ε)` is *Euclidean convex* — Mathlib's `UpperHalfPlane.image_coe_ball` identifies its image in
`ℂ` with the Euclidean disc `ball c.center ε (c.im * sinh ε)` — so its image is open and
preconnected, and two holomorphic functions on it which agree on a non-empty open subset agree
everywhere (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).
-/
import Mathlib
import Submission.Work.LayerCont.FarTail.Defs

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

/-- The image of an open set of `ℍ` under the inclusion `ℍ → ℂ` is open in `ℂ`.

Indeed the hyperbolic ball `B(v,ε)` maps onto the *Euclidean* disc of radius `v.im * sinh ε`
around `v.center ε` (`UpperHalfPlane.image_coe_ball`), which is open. -/
theorem coe_image_isOpen {V : Set UpperHalfPlane} (hV : IsOpen V) :
    IsOpen ((fun z : UpperHalfPlane => (z : ℂ)) '' V) := by
  have hUHP : IsOpen (Set.range (UpperHalfPlane.coe : UpperHalfPlane → ℂ)) := by
    rw [show Set.range (UpperHalfPlane.coe : UpperHalfPlane → ℂ) = {z : ℂ | 0 < z.im} from by
      ext z
      constructor
      · rintro ⟨w, rfl⟩; exact w.im_pos
      · intro hz; exact ⟨⟨z, hz⟩, rfl⟩]
    exact isOpen_lt continuous_const Complex.continuous_im
  exact (UpperHalfPlane.isEmbedding_coe.toIsInducing.isOpenMap hUHP) V hV

/-- The image of a hyperbolic ball in `ℂ` is preconnected (it is a Euclidean ball). -/
theorem isPreconnected_coe_ball (c : UpperHalfPlane) (ε : ℝ) :
    IsPreconnected ((fun z : UpperHalfPlane => (z : ℂ)) '' Metric.ball c ε) := by
  rw [UpperHalfPlane.image_coe_ball]
  exact Metric.isPreconnected_ball

/-- **Two holomorphic functions on a hyperbolic ball which agree on a non-empty open subset agree
everywhere.**

This is the identity theorem; it is the tool that lets one transport the far-side identity from one
chart to another with the same centre. -/
theorem eqOn_of_mdifferentiableOn_ball_of_eqOn {c : UpperHalfPlane} {ε : ℝ}
    {F G : UpperHalfPlane → ℂ}
    (hF : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
      (Metric.ball c ε))
    (hG : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G
      (Metric.ball c ε))
    {V : Set UpperHalfPlane} (hVsub : V ⊆ Metric.ball c ε) (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hV : Set.EqOn F G V) :
    Set.EqOn F G (Metric.ball c ε) := by
  set U : Set ℂ := (fun z : UpperHalfPlane => (z : ℂ)) '' Metric.ball c ε with hU
  have hUopen : IsOpen U := by
    rw [hU]; exact coe_image_isOpen Metric.isOpen_ball
  have hUconn : IsPreconnected U := by
    rw [hU]; exact isPreconnected_coe_ball c ε
  have hdiffF : DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex) U := by
    intro z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hF.mdifferentiableAt (s := Metric.ball c ε)
        (Metric.isOpen_ball.mem_nhds hτ))).differentiableWithinAt
  have hdiffG : DifferentiableOn ℂ (G ∘ UpperHalfPlane.ofComplex) U := by
    intro z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hG.mdifferentiableAt (s := Metric.ball c ε)
        (Metric.isOpen_ball.mem_nhds hτ))).differentiableWithinAt
  obtain ⟨v, hv⟩ := hVne
  have hvU : (v : ℂ) ∈ U := ⟨v, hVsub hv, rfl⟩
  have hvimg : (v : ℂ) ∈ (fun z : UpperHalfPlane => (z : ℂ)) '' V := ⟨v, hv, rfl⟩
  have hev : (F ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (v : ℂ)]
      (G ∘ UpperHalfPlane.ofComplex) := by
    filter_upwards [(coe_image_isOpen hVopen).mem_nhds hvimg] with z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : UpperHalfPlane.ofComplex (w : ℂ) = w := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos w.im_pos]
    simp only [Function.comp_apply, hw']
    exact hV hw
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hdiffF.analyticOnNhd hUopen) (hdiffG.analyticOnNhd hUopen) hUconn hvU hev
  intro τ hτ
  have h := hEqOn ⟨τ, hτ, rfl⟩
  have hτ' : UpperHalfPlane.ofComplex (τ : ℂ) = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  simpa only [Function.comp_apply, hτ'] using h

end Work.LayerCont.FarTail
