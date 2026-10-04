import Mathlib
import Submission.Work.Diff.C.ShapeAux.Kit
import Submission.Work.Diff.C.ray_cos_compare
import Submission.Work.Diff.C.grad_smoothAt
import Submission.JacobiCoords
import Submission.GExpFlow
import Submission.ChartCoordsTrans

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.ShapeAux

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative

/-- **The velocity field of a `C^∞` curve is smooth along the curve.**
In the chart at `c t`, the coordinates of the velocity are the derivative of the chart
coordinates of the curve, hence `C^∞`. -/
theorem smoothAlongAt_curveVelocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ) I ∞ c) (t : ℝ) :
    Submission.JacobiGlobal.SmoothAlongAt (I := I) c
      (fun s => Submission.Geodesic.curveVelocity (I := I) c s) t := by
  set z : M := c t with hz
  have hcont : ContinuousAt c t := hc.continuous.continuousAt
  have hsrcEv : ∀ᶠ s in 𝓝 t, c s ∈ (chartAt H z).source :=
    hcont.preimage_mem_nhds ((chartAt H z).open_source.mem_nhds (mem_chart_source H z))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hsrcEv
  have hsrc : ∀ s ∈ Metric.ball t ε, c s ∈ (chartAt H z).source := fun s hs => hεsub hs
  refine ⟨Metric.ball t ε, Metric.isOpen_ball, Metric.mem_ball_self hε, hsrc, ?_⟩
  have hγU : ContMDiffOn 𝓘(ℝ) I ∞ c (Metric.ball t ε) := hc.contMDiffOn
  set u : ℝ → E := fun s => (extChartAt I z) (c s) with hudef
  have hu : ContDiffOn ℝ ∞ u (Metric.ball t ε) := by
    have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => (extChartAt I z) (c s))
        (Metric.ball t ε) :=
      (contMDiffOn_extChartAt (I := I) (x := z)).comp hγU (fun s hs => hsrc s hs)
    exact h2.contDiffOn
  have ha : ContDiffOn ℝ ∞ (deriv u) (Metric.ball t ε) :=
    hu.deriv_of_isOpen Metric.isOpen_ball (le_of_eq (by simp))
  have hcd := Submission.ChartCoordsTrans.contDiffOn_chartCoords_frameVector (I := I)
    (z := z) (z' := z) (a := deriv u) (U := Metric.ball t ε) Metric.isOpen_ball ha hγU hsrc hsrc
  refine hcd.congr (fun s hs => ?_)
  have hmd : MDifferentiableAt 𝓘(ℝ) I c s := (hc.contMDiffAt).mdifferentiableAt (by simp)
  have hder := Submission.CurveField.deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity
    (I := I) (x := z) hmd (hsrc s hs)
  have hsrcE : c s ∈ (extChartAt I z).source := by rw [extChartAt_source]; exact hsrc s hs
  simp only [Submission.JacobiCoords.chartCoords, hudef]
  rw [hder, Submission.GExpFlow.frameVector_clm (I := I) hsrcE]

/-- **Second-order chain rule for a real function along a curve.**  If `f` is `C^∞` at `x` and `c`
is a `C^∞` curve with `c 0 = x` and non-vanishing velocity at `0`, then the second derivative of
`s ↦ f (c s)` at `0` is the Hessian of `f` at `x` applied to the velocity, plus the pairing of the
gradient with the covariant acceleration `∇_{c'}c'(0)` of `c`:
`(f ∘ c)''(0) = Hess f(c'(0), c'(0)) + ⟪∇f(x), ∇_{c'}c'(0)⟫`, where `Hess` is `Work.Diff.C.rhess`
(the covariant Hessian `⟪∇(∇f), ·⟫`) and `∇_{c'}c'(0)` is
`Submission.JacobiGlobal.covAlong cov (fun s => curveVelocity c s) 0`.

Route: `(f ∘ c)'(s) = mvfderiv f (c s) (c'(s)) = ⟪rgrad f (c s), c'(s)⟫` (chain rule,
`Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve` + `Work.Diff.C.inner_rgrad`); then
differentiate the pairing of the two fields along `c` by the product rule
(`Submission.Variation.hasDerivAt_inner_sections` after extending both fields to globally smooth
sections, `Submission.CurveField.exists_contMDiff_section_eventuallyEq_*`), using `covAlong_eq_cov`
to identify the covariant derivative of the gradient field with `cov (rgrad f) x (c'(0))` (this is
`rhess`) and of the velocity field with `covAlong`.  Note `hf : CMDiffAt ∞ f x` is the `∞`-notation
(`ContMDiffAt I 𝓘(ℝ,ℝ) ∞ f x`); lowering it with `hf.of_le` and
`contMDiffAt_iff_contMDiffOn_nhds` gives `C²`-regularity of `f` on a *neighbourhood* of `x`. -/
theorem deriv_deriv_comp_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {f : M → ℝ} {x : M} (hf : CMDiffAt ∞ f x)
    {c : ℝ → M} (hc0 : c 0 = x) (hc : ContMDiff 𝓘(ℝ) I ∞ c)
    (hne : Submission.Geodesic.curveVelocity (I := I) c 0 ≠ 0) :
    HasDerivAt (deriv (fun s : ℝ => f (c s)))
      (Work.Diff.C.rhess cov f x (Submission.Geodesic.curveVelocity (I := I) c 0)
          (Submission.Geodesic.curveVelocity (I := I) c 0)
        + Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f x)
            (Submission.JacobiGlobal.covAlong cov
              (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I) c s) 0)) 0 := by
  subst hc0
  -- extend the velocity to a globally smooth section
  obtain ⟨W, hWsm, hWev⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
      (I := I) (γ := c) (V := Set.univ) isOpen_univ (Set.mem_univ 0) hc.contMDiffOn hne
  have hWt : W (c 0) = Submission.Geodesic.curveVelocity (I := I) c 0 := hWev.self_of_nhds
  -- the gradient is smooth, hence differentiable, at the base point
  have hgrad : ContMDiffAt I I.tangent ∞
      (T% (fun y : M => Work.Diff.C.rgrad (I := I) f y)) (c 0) :=
    Work.Diff.C.grad_smoothAt hf
  have hfd : MDifferentiableAt I I.tangent
      (T% (fun y : M => Work.Diff.C.rgrad (I := I) f y)) (c 0) :=
    hgrad.mdifferentiableAt (by simp)
  have hWmd : MDifferentiableAt I I.tangent (T% W) (c 0) :=
    hWsm.contMDiffAt.mdifferentiableAt (by simp)
  -- the product rule for the metric pairing
  have hmain := Work.Diff.C.mvfderiv_inner_local (cov := cov) (x := c 0) (X := W)
    (σ := fun y : M => Work.Diff.C.rgrad (I := I) f y) (τ := W) hmet hfd hWmd
  -- the chain rule: derivative of the pairing along the curve
  have hcmd : MDifferentiableAt 𝓘(ℝ) I c 0 := hc.contMDiffAt.mdifferentiableAt (by simp)
  have hu : MDifferentiableAt I (𝓘(ℝ, ℝ))
      (fun y : M => Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f y) (W y)) (c 0) :=
    MDifferentiableAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x)
      (b := id) hfd hWmd
  have hcomp0 : HasDerivAt
      (fun τ : ℝ => Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f (c τ)) (W (c τ)))
      (mvfderiv I (fun y : M => Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f y) (W y))
        (c 0) (Submission.Geodesic.curveVelocity (I := I) c 0)) 0 := by
    have hstep := hu.hasMFDerivAt.comp 0 hcmd.hasMFDerivAt
    have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun y : M => Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f y) (W y))
      (γ := c) (t := 0) hu hcmd
    rw [show mvfderiv I
        (fun y : M => Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f y) (W y))
        (c 0) (Submission.Geodesic.curveVelocity (I := I) c 0)
        = deriv ((fun y : M => Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f y) (W y)) ∘ c) 0
        from hkey]
    exact hstep.hasFDerivAt.differentiableAt.hasDerivAt
  rw [← hWt, hmain, hWt] at hcomp0
  -- identify `cov W (c 0) (c'(0))` with `covAlong`
  have hsmooth : Submission.JacobiGlobal.SmoothAlongAt (I := I) c
      (fun s => Submission.Geodesic.curveVelocity (I := I) c s) 0 :=
    smoothAlongAt_curveVelocity (I := I) hc 0
  have hcovAlong : Submission.JacobiGlobal.covAlong cov
      (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I) c s) 0
      = cov W (c 0) (Submission.Geodesic.curveVelocity (I := I) c 0) :=
    Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor
      (hc.contMDiffOn.mono (Set.subset_univ _)) hne hsmooth hWsm hWev
  have hval : (Inner.inner ℝ (cov (fun y : M => Work.Diff.C.rgrad (I := I) f y) (c 0)
        (Submission.Geodesic.curveVelocity (I := I) c 0))
      (Submission.Geodesic.curveVelocity (I := I) c 0)
      + Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f (c 0))
        (cov W (c 0) (Submission.Geodesic.curveVelocity (I := I) c 0)))
      = (Work.Diff.C.rhess cov f (c 0) (Submission.Geodesic.curveVelocity (I := I) c 0)
          (Submission.Geodesic.curveVelocity (I := I) c 0)
        + Inner.inner ℝ (Work.Diff.C.rgrad (I := I) f (c 0))
            (Submission.JacobiGlobal.covAlong cov
              (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I) c s) 0)) := by
    rw [hcovAlong]
    rfl
  rw [hval] at hcomp0
  -- transfer to `deriv (f ∘ c)`
  refine hcomp0.congr_of_eventuallyEq ?_
  have hf1 : ∀ᶠ y in 𝓝 (c 0), ContMDiffAt I 𝓘(ℝ, ℝ) (1 : ℕ∞ω) f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (I := I) (I' := 𝓘(ℝ, ℝ)) (f := f) (x := c 0)
      (n := (1 : ℕ∞ω)) (by simp)).mp (hf.of_le (by simp))
  have hf1ev : ∀ᶠ τ in 𝓝 (0 : ℝ), MDifferentiableAt I 𝓘(ℝ, ℝ) f (c τ) :=
    ((hc.continuous.continuousAt.tendsto).eventually hf1).mono
      (fun τ h => h.mdifferentiableAt (by norm_num))
  filter_upwards [hWev, hf1ev] with τ hτW hτf
  have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := f)
    (γ := c) (t := τ) hτf ((hc.contMDiffAt).mdifferentiableAt (by simp))
  rw [← (show mvfderiv I f (c τ) (Submission.Geodesic.curveVelocity (I := I) c τ)
      = deriv (fun s : ℝ => f (c s)) τ from hkey), hτW]
  exact (Work.Diff.C.inner_rgrad_mvfderiv' (I := I) f (c τ)
    (Submission.Geodesic.curveVelocity (I := I) c τ)).symm

end Work.Diff.C.ShapeAux
