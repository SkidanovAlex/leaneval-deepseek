import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.step
import Submission.Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit
import Submission.Work.BasinSC.StepOneCrit.isConnected_diff_finite
import Submission.Work.BasinSC.StepOneCrit.Auxiliary
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap
import Submission.Work.BasinSC.StepOneCrit.uniformization_to_ball
import Submission.Work.Horn.isCoveringMapOn_restrictToPreimage
import Submission.Work.Horn.HB.component_homeo_of_covering_vnotin
import Submission.Work.Horn.HB.localComponent_ball_image
import Submission.Work.Horn.HB.isCompact_component_inter_preimage
import Submission.Work.Horn.HB.image_eq_of_proper_holomorphic
import Submission.Work.Horn.HB.aux1
import Submission.Work.Horn.HB.isCoveringMap_subtype_of_isClopen
import Submission.Work.Horn.HB.homeo_Vstar_puncturedDisc
import Submission.Work.Horn.HB.range_lift_eq_pathComponent
import Submission.Work.Horn.HB.LF_smaller_ball
import Submission.Work.Horn.HB.ambient_local_homeo
import Submission.Work.Horn.HB.exists_analytic_extension_of_bounded
import Submission.Work.Horn.HB.not_locally_const_of_covering_LF
import Submission.Work.Horn.HB.subsingleton_zeroSet_of_injOn_compl
import Submission.Work.Horn.HB.componentIn_ball_meets_fiber
import Submission.Work.Horn.HB.exists_mem_W_of_mem_ball
import Submission.Work.Horn.HB.proper_of_covering_LF
import Submission.Lib.Unif2.Work.Analysis.Complex.punctured_ball_connected
import Submission.Work.HornCov.isPreconnected_diff_critOrbit
import Submission.Lib.Unif2.Commons.Topology.Covering.natCard_fiber_eq_of_preconnected

/-!
# The component of a preimage under a covering map off `{0, v}` (HB4, duplicate copy)

This file carries the duplicate copy of the statement `Work.Horn.HB.proper_of_covering_LF` which the
project lead requested as an interchangeable second copy (see `HB/NOTES_HB5.md`: the wrapper
`Work.Horn.HB.covering_component_data_aux` in `basin_of_tower.lean` can be switched between the two
copies by changing two lines).

The statement is proved in this workspace, sorry-free and building, as
`Work.Horn.HB.proper_of_covering_LF`, whose development is `Submission/Work/Horn/HB/v_mem_case.lean`
together with its supporting files (`homeo_Vstar_puncturedDisc`,
`isCoveringMap_subtype_of_isClopen`, `range_lift_eq_pathComponent`, `lf_component_image`,
`infinite_fiber_of_gamma_eq_bot`, `exists_ncard_fiber_eq_of_gamma_ne_bot`,
`isCompact_preimage_of_isCoveringMap_finite`, `exists_unique_preimage_of_root`, ...).  The proof
splits exactly as follows.

* Case `v ∉ V`: the component `W` of `D ∩ g ⁻¹' V` through `x` is a covering of the simply connected
  `V`, hence a homeomorphism (`Work.Horn.HB.component_homeo_of_covering_vnotin`); this yields
  injectivity, surjectivity, properness and simple connectivity.
* Case `v ∈ V`: after uniformising `V ≅ 𝔻` with `v ↦ 0`, the deck analysis of the covering
  `W ∖ g ⁻¹' {v} → 𝔻*` (via `Work.BasinSC.CoverDisc`) shows it has finite degree `d`, the
  classification of coverings of `𝔻*` produces a `d`-th root `ψ` of the uniformising coordinate, and
  Riemann's removable-singularity theorem forces `g ⁻¹' {v} ∩ W` to be a single point `a`; with that
  point, the component of `D ∩ g ⁻¹' ball v ρ` inside `W` is unique, which gives properness, and
  Riemann–Hurwitz-lite (`Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit`
  resp. `Work.BasinSC.simplyConnected_of_proper_holomorphic_no_crit`) gives simple connectivity and
  the criticality statement.

The auxiliary lemmas of this area are verified in place in the shared library and were produced as
the pieces of this split: `Work.Horn.HB.not_locally_const_of_covering_LF`,
`Work.Horn.HB.subsingleton_zeroSet_of_injOn_compl`, `Work.Horn.HB.componentIn_ball_meets_fiber`,
`Work.Horn.HB.exists_mem_W_of_mem_ball` and `Work.Horn.HB.deriv_ne_zero_of_covering_off_critvals`.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology
open scoped Topology

theorem covering_component_data {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {r : ℝ}
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D) (hr : 0 < r) (hrv : r < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V) (hVsc : SimplyConnectedSpace V)
    (h0V : (0 : ℂ) ∉ V) {x : ℂ} (hxD : x ∈ D) (hxV : g x ∈ V) {W : Set ℂ}
    (hW : W = connectedComponentIn (D ∩ g ⁻¹' V) x) :
    (∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K)) ∧ V ⊆ g '' W ∧
      SimplyConnectedSpace W ∧ (v ∉ V → Set.InjOn g W) ∧
      (v ∈ V → ∃ a ∈ W, g a = v ∧ (∀ b ∈ W, g b = v → b = a) ∧
        (¬ Set.InjOn g W → deriv g a = 0)) :=
  Work.Horn.HB.proper_of_covering_LF hDo hgd hr hrv hcov hLF hVo hVc hVsc h0V hxD hxV hW

end Work.Horn.HB
