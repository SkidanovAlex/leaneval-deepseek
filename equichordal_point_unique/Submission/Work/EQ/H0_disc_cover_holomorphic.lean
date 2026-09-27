import Mathlib
import Submission.Work.EQ.H0_hyperbolic
import Submission.Work.EQ.H0_fatou
import Submission.Work.EQ.H0_regular_aux
import Submission.Work.EQ.cayley_homeomorph_uhp
import Submission.Work.EQ.CayleyUHPDefs
import Submission.Work.EQ.cayleyUHP_mdifferentiableAt
import Submission.Work.EQ.psiC_comp_differentiableAt

namespace Work.EQ

open scoped Manifold Topology
open _root_.Topology Complex Metric Filter

/-- **A holomorphic disc covering of a component of `H0`.**

Given a holomorphic covering `p : ℍ → S` of a component `S = connectedComponent P` of `H0` (as
produced by `Work.EQ.H0_component_uniformization` / `Work.EQ.exists_uniformizing_cover`), there is a
covering `q : 𝔻 → S` of `S` by the unit disc (via the Cayley transform,
`Work.EQ.cayley_homeomorph_uhp`) whose `ψ`-coordinate is holomorphic as a function on the disc: the
function `z ↦ psiC (discExt q z)` (which on `‖z‖ < 1` is `z ↦ psiC (q ⟨z, ·⟩)`) is complex
differentiable.

This discharges the hypothesis `hG` of `Work.EQ.good_ray_data` (after inverting, using that `psiC` is
nonzero on a component of `H0`).

The hypotheses `hpmd` and `hψmd` are the holomorphicity of the cover and of `ψ₁`; both are supplied
by the uniformization construction of `Work.EQ.H0_component_uniformization`
(`Work.EQ.UnivCover.mdifferentiable_pullChartedSpace` for `hψmd`), and are taken as hypotheses here
only to avoid having to match a particular `ChartedSpace` instance syntactically.

ROUTE.  Take `e : ↥(Metric.ball 0 1) ≃ₜ UpperHalfPlane` from `Work.EQ.cayley_homeomorph_uhp` and set
`q := p ∘ e`.  Then `q` is a covering map (`IsCoveringMap.comp_homeomorph`).

For `z₀` with `‖z₀‖ < 1`, put `F w := (⟨cayley w, cayley_im_pos ·⟩ : UpperHalfPlane)` for `‖w‖ < 1`
(so that `e ⟨w, ·⟩ = F w` by the explicit formula of `cayley_homeomorph_uhp`).

* `F` is a holomorphic map `ℂ → ℍ` near `z₀`: the charted space structure on `UpperHalfPlane` is
  `isOpenEmbedding_coe.singletonChartedSpace` (see
  `Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`), so
  `MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F z₀` follows from
  `DifferentiableAt ℂ (fun w => (F w : ℂ)) z₀`, i.e. from the differentiability of the rational
  function `w ↦ Complex.I * (1 + w) / (1 - w)` at `z₀` (`Work.EQ.one_sub_ne_zero` gives `1 - w ≠ 0`
  on the disc).  `UpperHalfPlane.mdifferentiableAt_ofComplex` and `UpperHalfPlane.contMDiffAt_iff`
  are the convenient restatements.
* Composing `hψmd` with `hpmd` gives `MDifferentiable` of `ψ₁ ∘ p ∘ F`, hence (the target being `ℂ`
  with the identity model) `DifferentiableOn ℂ (fun z => ψ₁ (p (F z))) (Metric.ball 0 1)`.
* `psiC` is locally `Γ ∘ ψ₁` with `Γ` analytic: `Work.EQ.psi_local_chart hsect` at the point
  `p (F z₀) ∈ H0` gives `Γ` and an eventual identity near that point; pull it back along the
  continuous map `z ↦ p (F z)` and compose `Γ` with the holomorphic `ψ₁ ∘ p ∘ F`. -/
theorem H0_disc_cover_holomorphic {a : ℝ} {h : ℂ → ℂ} {P : H0 a h}
    [ChartedSpace ℂ ↥(connectedComponent P)]
    (hsect : LocalSections a h)
    {p : UpperHalfPlane → ↥(connectedComponent P)} (hp : IsCoveringMap p)
    (hpmd : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) p)
    (hψmd : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun q : ↥(connectedComponent P) => ((q : H0 a h) : ChainData).2.1)) :
    ∃ q : Disc → ↥(connectedComponent P), IsCoveringMap q ∧
      DifferentiableOn ℂ (fun z : ℂ => psiC (discExt q z)) (Metric.ball (0 : ℂ) 1) := by
  -- the Cayley transform as a homeomorphism `𝔻 ≃ₜ ℍ`, with its explicit formula
  obtain ⟨e, hform, -⟩ := cayley_homeomorph_uhp
  -- the disc cover is `q := p ∘ e`, and it is a covering map
  refine ⟨fun u => p (e u), hp.comp_homeomorph e, ?_⟩
  intro z₀ hz₀
  have hz₀' : ‖z₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hz₀
  -- `discExt q` agrees near `z₀` with `p ∘ cayleyUHP`, because `e` is the Cayley transform
  have hev : (fun z : ℂ => psiC (p (cayleyUHP z))) =ᶠ[𝓝 z₀]
      (fun z : ℂ => psiC (discExt (fun u => p (e u)) z)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
    have hz1 : ‖z‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    rw [discExt_of_mem (fun u => p (e u)) hz]
    have hcoe : (e ⟨z, hz⟩ : ℂ) = (cayleyUHP z : ℂ) := by
      rw [hform ⟨z, hz⟩, cayleyUHP_coe hz1, cayley]
    have hthis : p (e ⟨z, hz⟩) = p (cayleyUHP z) := by
      congr 1
      exact UpperHalfPlane.coe_injective hcoe
    rw [hthis]
  -- `psiC ∘ p ∘ cayleyUHP` is complex differentiable at `z₀` by the local chart of `ψ`
  have hmain : DifferentiableAt ℂ (fun z : ℂ => psiC (p (cayleyUHP z))) z₀ :=
    psiC_comp_differentiableAt hsect hpmd hψmd (cayleyUHP_mdifferentiableAt hz₀')
  exact (hmain.congr_of_eventuallyEq hev.symm).differentiableWithinAt

end Work.EQ
