import ChallengeDeps
import Submission.Curvature
import Submission.Geodesic
import Submission.ChartConnection

/-!
# The chart geodesic equation versus the intrinsic geodesic equation

`Submission/Geodesic.lean` proves that a solution of the chart geodesic equation (in the chart at
`x₀`) satisfies the intrinsic geodesic equation `∇_{γ'}γ' = 0`.  Here we prove the **converse**:
if `γ` is an intrinsic geodesic (in the sense of `IsGeodesicAt`, i.e. `∇_Z := 0` for every smooth
section `Z` agreeing with the velocity along `γ`) and its coordinate curve in the chart at `x₀` is
`C²`, then the coordinate curve satisfies the chart equation `u'' = -Γ(u')(γ')`.

The key statement is an **identity**, `cov_apply_eq_frameVector`: for any smooth curve `γ` with
coordinate curve `u` and coordinate velocity `v` (`u' = v`, `v' = w`), and any smooth section `Z`
agreeing with the velocity of `γ` along the curve,

`∇_{γ'} Z = σ_{ w + Γ(v)(σ_v) }`,

where `σ_a` denotes `frameVector x₀ (γ t) a`.  Both directions of the equivalence
"chart geodesic ⟺ intrinsic geodesic" are immediate from it (the forward direction is
`cov_eq_zero_of_chartGeodesic` of `Submission/Geodesic.lean`; the backward direction uses
the injectivity of `frameVector`).

The statement is meaningless unless a smooth section agreeing with the velocity along a curve
exists; this is supplied by `Submission/CurveField.lean`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.ChartConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.Geodesic

noncomputable section

/-- **The chart form of the intrinsic geodesic equation.**  If `γ` is a smooth curve in the chart
at `x₀` with coordinate curve `u` (`u' = v`, `v' = w`) and `Z` is any smooth section agreeing with
the velocity of `γ` along the curve, then

`∇_{γ'(t)} Z = σ_{w + Γ(v)(σ_v)}`

where `σ_a = frameVector x₀ (γ t) a`; so the intrinsic equation `∇_{γ'}γ' = 0` is *equivalent* to
the chart equation `w = -Γ(v)(σ_v)`. -/

theorem cov_apply_eq_frameVector
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    {u v w : ℝ → E} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Ioo a b, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ioo a b, HasDerivAt v (w s) s)
    (hstay : ∀ s ∈ Ioo a b, u s ∈ (extChartAt I x₀).target)
    (Z : Π x : M, TangentSpace I x)
    (hZ : CMDiffAt ∞ (T% Z) ((extChartAt I x₀).symm (u t)))
    (hZeq : ∀ s ∈ Ioo a b, Z ((extChartAt I x₀).symm (u s)) =
      curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) s) :
    cov Z ((extChartAt I x₀).symm (u t))
      (curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) t)
      = frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (w t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (v t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (v t))) := by
  classical
  let γ : ℝ → M := fun s => (extChartAt I x₀).symm (u s)
  change cov Z (γ t) (curveVelocity (I := I) γ t)
    = frameVector (I := I) x₀ (γ t) (w t + christoffelEval cov x₀ (γ t) (v t)
        (frameVector (I := I) x₀ (γ t) (v t)))
  have hZeq' : ∀ s ∈ Ioo a b, Z (γ s) = curveVelocity (I := I) γ s := fun s hs => hZeq s hs
  have hZ' : CMDiffAt ∞ (T% Z) (γ t) := hZ
  have htgt : u t ∈ (extChartAt I x₀).target := hstay t ht
  have hmem : ∀ s ∈ Ioo a b, γ s ∈ (chartAt H x₀).source := by
    intro s hs
    have h1 := PartialEquiv.target_subset_preimage_source (extChartAt I x₀) (hstay s hs)
    rwa [extChartAt_source] at h1
  have hsrc : γ t ∈ (chartAt H x₀).source := hmem t ht
  have hOoo : Ioo a b ∈ 𝓝 t := IsOpen.mem_nhds isOpen_Ioo ht
  have hvelAt : ∀ s ∈ Ioo a b, curveVelocity (I := I) γ s = frameVector (I := I) x₀ (γ s) (v s) := by
    intro s hs
    have h := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := u) (t := s) (v := v s)
      (hu s hs) (hstay s hs)
      (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hs) (fun r hr => hstay r hr))
    simpa [frameVector, γ] using h
  have hnear : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    Filter.mem_of_superset hOoo (fun s hs => hstay s hs)
  have hvel : curveVelocity (I := I) γ t = frameVector (I := I) x₀ (γ t) (v t) := hvelAt t ht
  have hmdγ : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp (I := I) (x₀ := x₀)
      (u := u) (t := t) (v := v t) (hu t ht) htgt hnear).mdifferentiableAt
  -- the value of `Z` at `γ t`
  have hZval :
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (Z (γ t)) = v t := by
    have hcont : ContinuousAt (fun y : M =>
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)) (γ t) :=
      (contMDiffAt_continuousLinearMapAt_apply (I := I) x₀ hZ' hsrc).continuousAt
    have hT1 : Filter.Tendsto (fun s => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        (γ s) (Z (γ s))) (𝓝 t)
        (𝓝 ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (Z (γ t)))) :=
      (hcont.comp hmdγ.continuousAt).tendsto
    have hev : (fun s => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        (γ s) (Z (γ s))) =ᶠ[𝓝 t] v := by
      filter_upwards [hOoo] with s hs
      rw [hZeq' s hs, hvelAt s hs]
      exact continuousLinearMapAt_frameSection (I := I) x₀ (v s) (hmem s hs)
    have hT2 : Filter.Tendsto (fun s => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        (γ s) (Z (γ s))) (𝓝 t) (𝓝 (v t)) :=
      ((hv t ht).continuousAt.tendsto).congr' hev.symm
    exact tendsto_nhds_unique hT1 hT2
  -- the basis and the frame
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let σ : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x :=
    fun i => frameSection (I := I) x₀ (b i)
  let f : Fin (Module.finrank ℝ E) → M → ℝ := fun i y =>
    b.coord i ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))
  have hσsm : ∀ i, CMDiffAt ∞ (T% (σ i)) (γ t) := fun i => by
    simpa [σ] using contMDiffAt_frameSection (I := I) x₀ (b i) hsrc
  have hfsm : ∀ i, CMDiffAt ∞ (f i) (γ t) := fun i => by
    have hg := contMDiffAt_continuousLinearMapAt_apply (I := I) x₀ hZ' hsrc
    have hcomp : CMDiffAt ∞ (fun y : M =>
        ((b.coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap)
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))) (γ t) :=
      ContMDiffAt.comp (γ t)
        (ContinuousLinearMap.contMDiffAt ((b.coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap)) hg
    simpa [f, Function.comp, LinearMap.coe_toContinuousLinearMap'] using hcomp
  have hdec : Z =ᶠ[𝓝 (γ t)] fun y => ∑ i, f i y • σ i y := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hsrc] with y hy
    have h := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I) b x₀ Z hy
    simpa [f, σ, frameSection] using h
  have hmain :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
      (cov := cov) (s := Finset.univ) (f := f) (σ := σ) (Z := Z) (x := γ t)
      (v := curveVelocity (I := I) γ t) hZ' hσsm hfsm hdec
  have hfx : ∀ i, f i (γ t) = b.coord i (v t) := by
    intro i
    simp only [f, hZval]
  have hcov : ∀ i, cov (σ i) (γ t) (curveVelocity (I := I) γ t)
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t)) := by
    intro i
    have h := cov_frameSection_eq cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t) hsrc
    simpa only [σ, frameVector] using h
  have hder : ∀ i, mvfderiv I (f i) (γ t) (curveVelocity (I := I) γ t)
      = b.coord i (w t) := by
    intro i
    have hmdf : MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) (γ t) := (hfsm i).mdifferentiableAt (by simp)
    have hcomp := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) hmdf hmdγ
    have hcongr : deriv (f i ∘ γ) t = deriv (fun s => b.coord i (v s)) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hOoo] with s hs
      show f i (γ s) = b.coord i (v s)
      simp only [f]
      rw [hZeq' s hs, hvelAt s hs]
      exact congrArg (b.coord i) (continuousLinearMapAt_frameSection (I := I) x₀ (v s) (hmem s hs))
    have hlinear : deriv (fun s => b.coord i (v s)) t = b.coord i (w t) := by
      have hd : HasDerivAt (fun s => b.coord i (v s)) (b.coord i (w t)) t :=
        (((b.coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt
          t (hv t ht))
      exact hd.deriv
    change mvfderiv I (f i) (γ t) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) = b.coord i (w t)
    rw [hcomp, hcongr, hlinear]
  rw [hmain]
  have hS1 : (∑ i : Fin (Module.finrank ℝ E),
        f i (γ t) • cov (σ i) (γ t) (curveVelocity (I := I) γ t))
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (v t) (curveVelocity (I := I) γ t)) := by
    have h1 : (∑ i : Fin (Module.finrank ℝ E),
          f i (γ t) • cov (σ i) (γ t) (curveVelocity (I := I) γ t))
        = ∑ i, b.coord i (v t) • frameVector (I := I) x₀ (γ t)
            (christoffelEval cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t)) :=
      Finset.sum_congr rfl (fun i _ => by rw [hfx i, hcov i])
    have h2 : (∑ i, b.coord i (v t) • frameVector (I := I) x₀ (γ t)
            (christoffelEval cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t)))
        = frameVector (I := I) x₀ (γ t)
            (christoffelEval cov x₀ (γ t) (v t) (curveVelocity (I := I) γ t)) := by
      rw [← frameVector_sum, ← christoffelEval_sum_left Finset.univ cov x₀ (γ t)
        (fun i => b.coord i (v t)) (fun i => b i) (curveVelocity (I := I) γ t) hsrc]
      have hbv : (∑ i, b.coord i (v t) • b i) = v t := by
        simpa only [Module.Basis.coord_apply] using b.sum_repr (v t)
      rw [hbv]
    rw [h1, h2]
  have hS2 : (∑ i : Fin (Module.finrank ℝ E),
        mvfderiv I (f i) (γ t) (curveVelocity (I := I) γ t) • σ i (γ t))
      = frameVector (I := I) x₀ (γ t) (w t) := by
    have h1 : (∑ i : Fin (Module.finrank ℝ E),
          mvfderiv I (f i) (γ t) (curveVelocity (I := I) γ t) • σ i (γ t))
        = ∑ i, b.coord i (w t) • frameVector (I := I) x₀ (γ t) (b i) :=
      Finset.sum_congr rfl (fun i _ => by rw [hder i]; simp only [σ, frameSection, frameVector])
    have h2 : (∑ i, b.coord i (w t) • frameVector (I := I) x₀ (γ t) (b i))
        = frameVector (I := I) x₀ (γ t) (w t) := by
      rw [← frameVector_sum]
      have hbv : (∑ i, b.coord i (w t) • b i) = w t := by
        simpa only [Module.Basis.coord_apply] using b.sum_repr (w t)
      rw [hbv]
    rw [h1, h2]
  rw [hS1, hS2, ← frameVector_add, hvel]
  rw [add_comm]


/-- **The converse of `cov_eq_zero_of_chartGeodesic`.**  If `γ` is an intrinsic geodesic at the
time `t` (i.e. `∇_{γ'(t)}γ' = 0` in the sense of `IsGeodesicAt`) and its velocity field extends to
a smooth global section agreeing with it along the curve near `t`, then the coordinate curve `u`
of `γ` in the chart at `x₀` satisfies the chart geodesic equation at `t`:
`u''(t) = -Γ(u'(t))(γ'(t))`. -/
theorem chartGeodesicVectorField_eq_of_isGeodesicAt
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    {u v w : ℝ → E} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Ioo a b, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ioo a b, HasDerivAt v (w s) s)
    (hstay : ∀ s ∈ Ioo a b, u s ∈ (extChartAt I x₀).target)
    (Z : Π x : M, TangentSpace I x)
    (hZ : CMDiff ∞ (T% Z))
    (hZeq : ∀ s ∈ Ioo a b, Z ((extChartAt I x₀).symm (u s)) =
      curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) s)
    (hgeo : IsGeodesicAt cov (fun s => (extChartAt I x₀).symm (u s)) t) :
    w t = chartGeodesicVectorField cov x₀ (u t, v t) := by
  have h := cov_apply_eq_frameVector cov x₀ ht hu hv hstay Z hZ.contMDiffAt hZeq
  have h0 : cov Z ((extChartAt I x₀).symm (u t))
      (curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) t) = 0 :=
    hgeo Z hZ (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo ht) hZeq)
  rw [h0] at h
  have hfr : frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
      (w t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (v t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (v t))) = 0 := h.symm
  have hb : (extChartAt I x₀).symm (u t) ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_source_chartCurve (I := I) (x₀ := x₀) (hstay t ht)
  have hsum : w t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (v t)
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (v t)) = 0 := by
    have h1 := Trivialization.continuousLinearMapAt_symmL
      (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hb
      (w t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (v t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (v t)))
    rw [← h1]
    change (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
      ((extChartAt I x₀).symm (u t)) (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (w t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (v t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (v t)))) = 0
    rw [hfr]
    exact map_zero _
  have hchart : chartGeodesicVectorField cov x₀ (u t, v t)
      = -christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (v t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (v t)) := rfl
  rw [hchart]
  exact eq_neg_of_add_eq_zero_left hsum


end

end Submission.Geodesic
