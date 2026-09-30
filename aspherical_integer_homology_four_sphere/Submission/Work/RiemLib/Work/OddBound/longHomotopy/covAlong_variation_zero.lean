import Mathlib
import Submission.Work.RiemLib.Work.OddBound.LiftKit
import Submission.Work.RiemLib.RayJacobi
import Submission.Work.RiemLib.GExpVelocity
import Submission.Work.RiemLib.GExpRayZero
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.GeodesicExtend
import Submission.Work.RiemLib.JacobiCoords
import Submission.Work.RiemLib.IntrinsicVariation
import Submission.Work.RiemLib.BonnetMyers
import Submission.Work.RiemLib.SecondVariation
import Submission.Work.RiemLib.ChartCurv
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Analysis.Calculus.deriv_deriv_swap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **The variation field of the family of rays has covariant derivative `η` at `0`.**

For the family of geodesic rays `r ↦ exp_p (s • (u + r • η))`, the associated variation field
`V s = ∂_r|_{r=0} exp_p (s • (u + r • η))` is a Jacobi field along `γ s = exp_p (s • u)` with
`V 0 = 0`, and its covariant derivative at `0` is the perturbation direction `η`. -/
theorem covAlong_variation_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u η : TangentSpace I p} (hu : u ≠ 0) :
    Submission.JacobiGlobal.covAlong cov
      (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η))) 0) 0
      = η := by
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) with hγdef
  set V : (s : ℝ) → TangentSpace I (γ s) :=
    fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η))) 0 with hVdef
  rw [Submission.JacobiGlobal.covAlong]
  have hγ0 : γ 0 = p := by
    rw [hγdef]
    simp only [zero_smul, Submission.GlobalExp.GExp_zero]
  have hV0 : V 0 = 0 := by
    rw [hVdef]
    simp only []
    have hev : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((0:ℝ) • (u + r • η)))
        =ᶠ[𝓝 (0:ℝ)] (fun _ : ℝ => p) := by
      filter_upwards with r
      rw [zero_smul, Submission.GlobalExp.GExp_zero]
    rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev,
      Submission.Geodesic.curveVelocity_const]
  have hc0 : Submission.JacobiCoords.chartCoords (I := I) p γ V 0 = 0 := by
    rw [Submission.JacobiCoords.chartCoords]
    rw [hV0]
    exact map_zero _
  rw [hγ0]
  have hDtQ : Submission.BonnetMyers.DtQ cov p (Submission.IntrinsicVariation.chartCoord (I := I) p γ)
      (Submission.JacobiCoords.chartCoords (I := I) p γ V)
      (deriv (Submission.IntrinsicVariation.chartCoord (I := I) p γ))
      (deriv (Submission.JacobiCoords.chartCoords (I := I) p γ V)) 0
      = deriv (Submission.JacobiCoords.chartCoords (I := I) p γ V) 0 := by
    simp only [Submission.BonnetMyers.DtQ, Submission.SecondVariation.covDsP,
      Submission.SecondVariation.fam, Submission.SecondVariation.famP, zero_smul, add_zero]
    rw [hc0, Submission.ChartCurv.chrB_zero_snd, add_zero]
  rw [hDtQ]
  have hkey : deriv (Submission.JacobiCoords.chartCoords (I := I) p γ V) 0
      = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η := by
    set Ψ : ℝ × ℝ → E := fun q : ℝ × ℝ =>
      (extChartAt I p) (Submission.GlobalExp.GExp (cov := cov) hmet p (q.1 • (u + q.2 • η))) with hΨdef
    have hΨcd : ContDiffAt ℝ 2 Ψ (0, 0) := by
      have hsrc : Submission.GlobalExp.GExp (cov := cov) hmet p ((0:ℝ) • (u + (0:ℝ) • η)) ∈ (chartAt H p).source := by
        rw [zero_smul, Submission.GlobalExp.GExp_zero]
        exact mem_chart_source H p
      rw [hΨdef]
      exact (Submission.RayJacobi.contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η)
        (x₀ := p) (σ := 0) (ρ := 0) hsrc).of_le (WithTop.coe_le_coe.mpr le_top)
    have hγcont : ContinuousAt γ 0 := by
      have h1 : ContinuousAt (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 0 :=
        (contMDiffOn_univ.mp (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hu)).continuous.continuousAt
      refine h1.congr ?_
      filter_upwards with s
      show Submission.GlobalExp.GExp (cov := cov) hmet p (s • u) = γ s
      rw [hγdef]
      simp only [zero_smul, add_zero]
    have hsrcev : ∀ᶠ s in 𝓝 (0:ℝ), γ s ∈ (chartAt H p).source :=
      hγcont.preimage_mem_nhds
        ((chartAt H p).open_source.mem_nhds (by rw [hγ0]; exact mem_chart_source H p))
    have hev : (fun s : ℝ => Submission.JacobiCoords.chartCoords (I := I) p γ V s)
        =ᶠ[𝓝 (0:ℝ)] (fun s : ℝ => deriv (fun r : ℝ => Ψ (s, r)) 0) := by
      filter_upwards [hsrcev] with s hs
      have hsrce : γ s ∈ (extChartAt I p).source := by rwa [extChartAt_source]
      have hb : γ s ∈ (trivializationAt E (TangentSpace I) p).baseSet := by simpa using hs
      have hΨs0 : Ψ (s, 0) = (extChartAt I p) (γ s) := by
        show (extChartAt I p) (Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
          = (extChartAt I p) (γ s)
        rw [hγdef]
      have hbase : (extChartAt I p).symm (Ψ (s, 0)) = γ s := by
        rw [hΨs0]
        exact (extChartAt I p).left_inv hsrce
      have htgt : Ψ (s, 0) ∈ (extChartAt I p).target := by
        rw [hΨs0]
        exact (extChartAt I p).map_source hsrce
      have hcd_s : ContDiffAt ℝ ∞ Ψ (s, 0) := by
        rw [hΨdef]
        exact Submission.RayJacobi.contDiffAt_chartFamily (cov := cov) hmet (p := p) (u := u) (η := η)
          (x₀ := p) (σ := s) (ρ := 0) (by simpa [hγdef] using hs)
      have hGcont : ContinuousAt
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η))) 0 := by
        have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := p) (u := u) (η := η) s 0
        have h : ContinuousAt (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η))) 0 :=
          (hfam.continuousAt).comp (by fun_prop : ContinuousAt (fun r : ℝ => (s, r)) 0)
        exact h
      have hGsrc : ∀ᶠ r in 𝓝 (0:ℝ),
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η)) ∈ (extChartAt I p).source := by
        have hbase' : Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)) ∈ (chartAt H p).source := by
          simpa [hγdef] using hs
        filter_upwards [hGcont.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hbase')] with r hr
        rwa [extChartAt_source]
      have hstay : ∀ᶠ r in 𝓝 (0:ℝ), Ψ (s, r) ∈ (extChartAt I p).target := by
        filter_upwards [hGsrc] with r hr
        rw [hΨdef]
        simp only []
        exact (extChartAt I p).map_source hr
      have hderiv_s : HasDerivAt (fun r : ℝ => Ψ (s, r)) (deriv (fun r : ℝ => Ψ (s, r)) 0) 0 := by
        have hd : DifferentiableAt ℝ Ψ (s, 0) := hcd_s.differentiableAt (by simp)
        have hd' : DifferentiableAt ℝ (fun r : ℝ => Ψ (s, r)) 0 :=
          hd.comp 0 (by fun_prop : DifferentiableAt ℝ (fun r : ℝ => (s, r)) 0)
        simpa [Function.comp_def] using hd'.hasDerivAt
      have hcv := Submission.Geodesic.curveVelocity_extChartAt_symm (I := I) (x₀ := p)
        (u := fun r : ℝ => Ψ (s, r)) (t := 0) (v := deriv (fun r : ℝ => Ψ (s, r)) 0)
        hderiv_s htgt hstay
      have hgerm : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η)))
          =ᶠ[𝓝 (0:ℝ)] (fun r : ℝ => (extChartAt I p).symm (Ψ (s, r))) := by
        filter_upwards [hGsrc] with r hr
        rw [hΨdef]
        simp only []
        exact ((extChartAt I p).left_inv hr).symm
      calc Submission.JacobiCoords.chartCoords (I := I) p γ V s
          = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ s) (V s) := by
            rw [Submission.JacobiCoords.chartCoords]
        _ = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ s)
              (Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + r • η))) 0) := by
            rw [hVdef]
        _ = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ s)
              (Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => (extChartAt I p).symm (Ψ (s, r))) 0) := by
            rw [Submission.RayJacobi.curveVelocity_congr (I := I) hgerm]
        _ = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ s)
              ((Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) p)
                ((extChartAt I p).symm (Ψ (s, 0)))) (deriv (fun r : ℝ => Ψ (s, r)) 0)) := by
            rw [hcv]
        _ = (Trivialization.continuousLinearMapAt ℝ (trivializationAt E (TangentSpace I) p) (γ s))
              ((Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) p) (γ s))
                (deriv (fun r : ℝ => Ψ (s, r)) 0)) := by
            rw [hbase]
        _ = deriv (fun r : ℝ => Ψ (s, r)) 0 :=
            Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) p) hb _
    have hu_ne : ∀ᶠ t in 𝓝 (0:ℝ), u + t • η ≠ 0 := by
      have hmem : {w : TangentSpace I p | w ≠ 0} ∈ 𝓝 (u + (0:ℝ) • η) := by
        simpa using isOpen_ne.mem_nhds hu
      have hcont : Continuous (fun t : ℝ => u + t • η) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds hmem
    have hpartial : (fun t : ℝ => deriv (fun s : ℝ => Ψ (s, t)) 0)
        =ᶠ[𝓝 (0:ℝ)]
        (fun t : ℝ => (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p (u + t • η)) := by
      filter_upwards [hu_ne] with t hvt
      have hvel : Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + t • η))) 0 = u + t • η :=
        Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hvt
      have hmd : MDiffAt (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + t • η))) 0 :=
        (contMDiffOn_univ.mp (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hvt)).mdifferentiableAt (by simp)
      have hsrcp : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + t • η))) 0 ∈ (chartAt H p).source := by
        show Submission.GlobalExp.GExp (cov := cov) hmet p ((0:ℝ) • (u + t • η)) ∈ (chartAt H p).source
        rw [zero_smul, Submission.GlobalExp.GExp_zero]
        exact mem_chart_source H p
      have hclm := Submission.Geodesic.continuousLinearMapAt_curveVelocity (I := I) (x₀ := p)
        (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + t • η))) (t := 0) hmd hsrcp
      rw [hvel] at hclm
      rw [show Submission.GlobalExp.GExp (cov := cov) hmet p ((0:ℝ) • (u + t • η)) = p from by
            rw [zero_smul, Submission.GlobalExp.GExp_zero]] at hclm
      have h2 : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E)
            ((extChartAt I p) ∘ (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • (u + t • η)))) (0:ℝ)) (1:ℝ)
          = deriv (fun s : ℝ => Ψ (s, t)) 0 := by
        rw [mfderiv_eq_fderiv, hΨdef]
        rfl
      exact h2.symm.trans hclm.symm
    have hclmderiv : HasDerivAt
        (fun t : ℝ => (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p (u + t • η))
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • η) ((1:ℝ) • η) 0 := (hasDerivAt_id (0:ℝ)).smul_const η
      have h2 : HasDerivAt (fun t : ℝ => u + t • η) η 0 := by simpa using h1.const_add u
      exact (ContinuousLinearMap.hasFDerivAt
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p)).comp_hasDerivAt (0:ℝ) h2
    calc deriv (Submission.JacobiCoords.chartCoords (I := I) p γ V) 0
        = deriv (fun s : ℝ => deriv (fun r : ℝ => Ψ (s, r)) 0) 0 := hev.deriv_eq
      _ = deriv (fun t : ℝ => deriv (fun s : ℝ => Ψ (s, t)) 0) 0 :=
            (Commons.Analysis.Calculus.deriv_deriv_swap hΨcd).symm
      _ = deriv (fun t : ℝ => (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p (u + t • η)) 0 :=
            hpartial.deriv_eq
      _ = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η := hclmderiv.deriv
  rw [hkey]
  exact Submission.GExpFlow.frameVector_clm (I := I) (z₀ := p) (q := p)
    (by rw [extChartAt_source]; exact mem_chart_source H p) η

end Work.OddBound.longHomotopy
