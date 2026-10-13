import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

/-- The composition of an analytic `Ψ` with the affine complex curve `t ↦ u₀ + t • w` is analytic.
`eaEvalC c f` is entire (`Work.WilE3.API.eaEvalC_fderiv_analytic`), so the whole composite is
analytic at `0`. -/
theorem analyticAt_curveFun {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (f : WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨan : AnalyticAt ℂ Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0))
    (w : Work.WilE3.Frame.U k ι → ℝ) :
    AnalyticAt ℂ (fun t : ℂ => Work.WilE3.eaEvalC c f
      (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)
          + t • (fun i => (w i : ℂ)), 0))) 0 := by
  -- The affine curve `γ t = (u₀ + t • w, 0)` is analytic at `0`: it is a constant plus a scalar
  -- multiple of the identity.
  have hγ : AnalyticAt ℂ (fun t : ℂ =>
      ((Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)
          + t • (fun i => (w i : ℂ))), (0 : Fin j → ℂ))) 0 := by
    refine (analyticAt_const.add ?_).prod analyticAt_const
    exact analyticAt_id.smul analyticAt_const
  -- `Ψ` is analytic at the value `γ 0` of the curve.
  have hΨ' : AnalyticAt ℂ Ψ ((fun t : ℂ =>
      ((Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)
          + t • (fun i => (w i : ℂ))), (0 : Fin j → ℂ))) 0) := by
    simpa using hΨan
  have hcurve : AnalyticAt ℂ (fun t : ℂ => Ψ
      (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)
          + t • (fun i => (w i : ℂ)), 0)) 0 :=
    AnalyticAt.comp (x := (0 : ℂ)) hΨ' hγ
  -- Compose with the entire function `eaEvalC c f`.
  exact AnalyticAt.comp (x := (0 : ℂ))
    (f := fun t : ℂ => Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)
          + t • (fun i => (w i : ℂ)), 0))
    ((Work.WilE3.API.eaEvalC_fderiv_analytic c f _).1) hcurve

end Work.WilE3.Frame
