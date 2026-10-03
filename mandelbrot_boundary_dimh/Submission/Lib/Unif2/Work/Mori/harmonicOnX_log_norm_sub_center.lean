import Submission.Lib.Unif2.Work.Mori.PeriodHom
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic

/-!
# `log ‖z - p‖` is harmonic on a plane domain avoiding `p`

`Work.Mori.harmonicOnX_log_norm_sub_center`: for an open `U ⊆ ℂ` and a point `p ∉ U`, the function
`z ↦ log ‖z - p‖` is harmonic on the one-dimensional complex manifold `U`.  This is what makes
`Work.Mori.conjPeriodHomOf` applicable to it, producing the argument-period (winding) homomorphism
`Work.Mori.argumentPeriodHom` of a plane domain around an exterior point.

The proof is the same localisation as `Work.Modulus.puncturedHarmonic`: the chart of the open subset
`U` is the restriction of the identity chart of `ℂ` (`Work.Modulus.opensChartAt_symm_eqOn`,
`Work.Modulus.opensChartAt_apply`), where the function is `log ‖·‖` of the nowhere-zero analytic
function `w ↦ w - p` (`AnalyticAt.harmonicAt_log_norm`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

/-- **`log ‖z - p‖` is harmonic on a plane domain that avoids `p`.** -/
theorem harmonicOnX_log_norm_sub_center (U : TopologicalSpace.Opens ℂ) (p : ℂ)
    (hp : p ∉ (U : Set ℂ)) :
    Submission.HarmonicOnX (fun z : U => Real.log ‖(z : ℂ) - p‖) Set.univ := by
  intro u _
  change InnerProductSpace.HarmonicAt
    ((fun z : U => Real.log ‖(z : ℂ) - p‖) ∘ (chartAt ℂ u).symm) ((chartAt ℂ u) u)
  have haz : AnalyticAt ℂ (fun w : ℂ => w - p) ((u : U) : ℂ) :=
    analyticAt_id.sub analyticAt_const
  have hne : (((u : U) : ℂ) - p) ≠ 0 :=
    sub_ne_zero.mpr fun h => hp (h ▸ u.2)
  have hat : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w - p‖) ((u : U) : ℂ) :=
    haz.harmonicAt_log_norm hne
  have heq : ((fun z : U => Real.log ‖(z : ℂ) - p‖) ∘ (chartAt ℂ u).symm)
      =ᶠ[𝓝 ((chartAt ℂ ((u : U) : ℂ)) ((u : U) : ℂ))] (fun w : ℂ => Real.log ‖w - p‖) := by
    filter_upwards [(chartAt ℂ u).open_target.mem_nhds
      (Work.Modulus.opensChartAt_mem_target U u)] with z hz
    simp only [Function.comp_apply]
    rw [Work.Modulus.opensChartAt_symm_eqOn U u hz]
    rfl
  rw [Work.Modulus.opensChartAt_apply U u]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hat

end Work.Mori
