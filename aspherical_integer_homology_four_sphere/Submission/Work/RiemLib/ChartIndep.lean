import Submission.Work.RiemLib.RayJacobiTensor
import Submission.Work.RiemLib.GlobalBM

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Chart-independence of the Jacobi equation

`Submission.RauchGlobal.IsJacobiAt` defines "`J` is a Jacobi field along `γ` near `t`" as an
**existential over charts**: *some* chart carries the equation `D(Dy) + R(y,w)w = 0` near `t`.  What
the chart-based developments need — in particular `Submission.IndexCorner2`, and hence the global
`σ ≤ κ` of `Submission/Roadmap.lean` §95.3 — is the converse: the equation can be *read in any chart*
containing the curve.

The geodesic equation has the same issue, and it was solved in `Submission/GeodesicExtend` by writing
the equation intrinsically (`∇_{γ'}γ' = 0`) and *computing* the chart equation from it.  There is no
intrinsic Jacobi equation in the library, so this file uses the next best thing: the **intrinsic
formula for `∇` of a global smooth section** (`Submission.ChartCurv.cov_eq_frameVector_coordFun`).

* `frameVector_chartCovDeriv_eq_cov` — **the bridge**: if a globally smooth section `W` agrees along
  `γ` near `t₀` with the field whose chart-`x₀` coordinates are `y`, then
  `σ_{w' + Γ(y)(w)} = ∇_{γ'}W (γ t₀)`, i.e. the chart expression for the covariant derivative along a
  curve *is* the intrinsic one.  The right-hand side mentions no chart, so the left-hand side is
  chart-independent;
* `chartCovDeriv_coordFun_eq_of_charts` — hence the covariant derivative along a curve computed in two
  charts (through the same global section) is the same tangent vector;
* `frameVector_chartCurv_eq_of_charts` — the curvature term of the Jacobi equation is chart-independent
  (`curvVec_frameVector_eq` computes `chartCurv` as the intrinsic `curvVec`);
* `frameVector_chartJacobi_eq_of_charts` — the whole **chart Jacobi expression** is chart-independent;
* **`chartJacobiEquation_of_charts`** — **the chart Jacobi equation is chart-independent**: if it
  holds in one chart containing the curve, it holds in any other.

The statements take two global sections as hypotheses: `W` agreeing with `J` along `γ`, and `Z`
agreeing with `∇_{γ'}J`.  This is what keeps them assumption-light: the second covariant derivative is
applied to the *coordinates of `Z`* rather than to the chart expression `chartCovDeriv y`, so no
smoothness of the intermediate coordinate function is needed.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.Jacobi
open Submission.Rauch

namespace Submission.ChartIndep

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless]

/-- **The chart formula for the covariant derivative along a curve is intrinsic.**  If a globally
smooth section `W` agrees along `γ` near `t₀` with the field whose chart-`x₀` coordinates are `y`,
then the chart formula `w' + Γ(y)(w)` *is* `∇_{γ'}W` at `t₀`.

This is the bridge that makes `chartCovDeriv` (and hence the chart Jacobi equation) chart-independent:
the right-hand side does not mention `x₀` at all. -/
theorem frameVector_chartCovDeriv_eq_cov
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {t₀ : ℝ} {x₀ : M} (hsrc : γ t₀ ∈ (chartAt H x₀).source)
    (hsrcEv : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₀).source)
    {u w y : ℝ → E}
    (huTgt : ∀ᶠ s in 𝓝 t₀, u s ∈ (extChartAt I x₀).target) {W : Π x : M, TangentSpace I x} (hWsm : CMDiff ∞ (T% W))
    (hγ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t₀, HasDerivAt u (w s) s)
    (hy : ∀ᶠ s in 𝓝 t₀, frameVector (I := I) x₀ (γ s) (y s) = W (γ s))
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀) :
    frameVector (I := I) x₀ (γ t₀) (chartCovDeriv cov x₀ u w y t₀)
      = cov W (γ t₀) (curveVelocity (I := I) γ t₀) := by
  -- the coordinates of `W` along `γ` agree with `y`
  have hcoord : ∀ᶠ s in 𝓝 t₀, coordFun x₀ W (γ s) = y s := by
    filter_upwards [hy, hsrcEv] with s hy' hs'
    have h1 : frameVector (I := I) x₀ (γ s) (coordFun x₀ W (γ s)) = W (γ s) :=
      frameVector_coordFun_eq (x₀ := x₀) hs'
    rw [← h1] at hy'
    have h2 := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ s)) hy'
    have h3 : ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ s))
        (frameVector (I := I) x₀ (γ s) (y s)) = y s :=
      GlobalBM.continuousLinearMapAt_frameVector (I := I) x₀ (γ s) hs' (y s)
    have h4 : ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ s))
        (frameVector (I := I) x₀ (γ s) (coordFun x₀ W (γ s))) = coordFun x₀ W (γ s) :=
      GlobalBM.continuousLinearMapAt_frameVector (I := I) x₀ (γ s) hs' (coordFun x₀ W (γ s))
    rw [h3, h4] at h2
    exact h2.symm
  -- the chart velocity of `u` is that of `γ`
  have hγvel : deriv (fun s => (extChartAt I x₀) (γ s)) t₀ = w t₀ := by
    have hev : (fun s => (extChartAt I x₀) (γ s)) =ᶠ[𝓝 t₀] u := by
      filter_upwards [hγ, huTgt] with s hs ht
      rw [hs]
      exact PartialEquiv.right_inv (extChartAt I x₀) ht
    rw [hev.deriv_eq]
    exact (hu.self_of_nhds).deriv
  -- the chart coordinate vector of the velocity is the velocity
  have hvel : frameVector (I := I) x₀ (γ t₀) (w t₀) = curveVelocity (I := I) γ t₀ := by
    rw [← hγvel,
      GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) x₀ hγmd hsrc,
      GlobalBM.frameVector_continuousLinearMapAt (I := I) x₀ (γ t₀) hsrc]
  -- the intrinsic formula for `∇_v W`
  have h1 := cov_eq_frameVector_coordFun (cov := cov) (x₀ := x₀) (W := W) hWsm hsrc (v := w t₀)
  rw [hvel] at h1
  rw [h1]
  congr 1
  -- identify the two coordinate expressions
  rw [chartCovDeriv_apply (cov := cov) (x₀ := x₀) huTgt.self_of_nhds, ← hγ.eq_of_nhds,
    chrB_apply, hcoord.self_of_nhds]
  congr 1
  change deriv y t₀ = mvfderiv I (coordFun x₀ W) (γ t₀) ((mfderiv 𝓘(ℝ) I γ t₀) (1 : ℝ))
  rw [Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
    (g := coordFun x₀ W) (γ := γ) (t := t₀)
    ((contMDiffAt_coordFun (x₀ := x₀) hWsm hsrc).mdifferentiableAt (by simp)) hγmd]
  exact (Filter.EventuallyEq.deriv_eq hcoord).symm

/-! ## Chart-independence

The bridge `frameVector_chartCovDeriv_eq_cov` identifies the chart expression with the intrinsic
`cov W (γ t₀) (curveVelocity γ t₀)`, which mentions no chart at all.  Comparing the bridge in two
charts gives the **chart-independence of the covariant derivative along a curve**; the curvature term
is chart-independent by `curvVec_frameVector_eq`. -/

/-- **Chart-independence of the covariant derivative along a curve** (through a global section `W`):
the chart formulas `w' + Γ(y)(w)` for the coordinates of `W` in two charts give the same tangent
vector. -/
theorem chartCovDeriv_coordFun_eq_of_charts
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {W : Π x : M, TangentSpace I x} (hWsm : CMDiff ∞ (T% W))
    {γ : ℝ → M} {t₀ : ℝ} (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    {x₀ x₁ : M} (hsrc₀ : γ t₀ ∈ (chartAt H x₀).source)
    (hsrc₁ : γ t₀ ∈ (chartAt H x₁).source)
    (hsrcEv₀ : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₀).source)
    (hsrcEv₁ : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₁).source)
    {u₀ w₀ u₁ w₁ : ℝ → E}
    (huTgt₀ : ∀ᶠ s in 𝓝 t₀, u₀ s ∈ (extChartAt I x₀).target)
    (huTgt₁ : ∀ᶠ s in 𝓝 t₀, u₁ s ∈ (extChartAt I x₁).target)
    (hγ₀ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₀).symm (u₀ s))
    (hγ₁ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₁).symm (u₁ s))
    (hu₀ : ∀ᶠ s in 𝓝 t₀, HasDerivAt u₀ (w₀ s) s)
    (hu₁ : ∀ᶠ s in 𝓝 t₀, HasDerivAt u₁ (w₁ s) s) :
    frameVector (I := I) x₀ (γ t₀)
        (chartCovDeriv cov x₀ u₀ w₀ (fun s => coordFun x₀ W (γ s)) t₀)
      = frameVector (I := I) x₁ (γ t₀)
        (chartCovDeriv cov x₁ u₁ w₁ (fun s => coordFun x₁ W (γ s)) t₀) := by
  rw [frameVector_chartCovDeriv_eq_cov (cov := cov) hsrc₀ hsrcEv₀ huTgt₀ hWsm hγ₀ hu₀
        (by filter_upwards [hsrcEv₀] with s hs
            exact frameVector_coordFun_eq (x₀ := x₀) hs) hγmd,
      frameVector_chartCovDeriv_eq_cov (cov := cov) hsrc₁ hsrcEv₁ huTgt₁ hWsm hγ₁ hu₁
        (by filter_upwards [hsrcEv₁] with s hs
            exact frameVector_coordFun_eq (x₀ := x₁) hs) hγmd]

/-- **Chart-independence of the curvature term** of the Jacobi equation. -/
theorem frameVector_chartCurv_eq_of_charts
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {t₀ : ℝ} {x₀ x₁ : M}
    (hsrc₀ : γ t₀ ∈ (chartAt H x₀).source) (hsrc₁ : γ t₀ ∈ (chartAt H x₁).source)
    {X₀ Y₀ X₁ Y₁ : E}
    (hX : frameVector (I := I) x₀ (γ t₀) X₀ = frameVector (I := I) x₁ (γ t₀) X₁)
    (hY : frameVector (I := I) x₀ (γ t₀) Y₀ = frameVector (I := I) x₁ (γ t₀) Y₁) :
    frameVector (I := I) x₀ (γ t₀) (chartCurv cov x₀ (γ t₀) X₀ Y₀)
      = frameVector (I := I) x₁ (γ t₀) (chartCurv cov x₁ (γ t₀) X₁ Y₁) := by
  rw [← curvVec_frameVector_eq (cov := cov) htor x₀ hsrc₀ X₀ Y₀,
    ← curvVec_frameVector_eq (cov := cov) htor x₁ hsrc₁ X₁ Y₁, hX, hY]

/-- The chart coordinate vector of the velocity of a curve in a chart is the velocity itself. -/
theorem frameVector_chartVel_eq_curveVelocity
    {γ : ℝ → M} {t₀ : ℝ} {x₀ : M} (hsrc : γ t₀ ∈ (chartAt H x₀).source)
    {u w : ℝ → E} (huTgt : ∀ᶠ s in 𝓝 t₀, u s ∈ (extChartAt I x₀).target)
    (hγ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t₀, HasDerivAt u (w s) s)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀) :
    frameVector (I := I) x₀ (γ t₀) (w t₀) = curveVelocity (I := I) γ t₀ := by
  have hγvel : deriv (fun s => (extChartAt I x₀) (γ s)) t₀ = w t₀ := by
    have hev : (fun s => (extChartAt I x₀) (γ s)) =ᶠ[𝓝 t₀] u := by
      filter_upwards [hγ, huTgt] with s hs ht
      rw [hs]
      exact PartialEquiv.right_inv (extChartAt I x₀) ht
    rw [hev.deriv_eq]
    exact (hu.self_of_nhds).deriv
  rw [← hγvel,
    GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) x₀ hγmd hsrc,
    GlobalBM.frameVector_continuousLinearMapAt (I := I) x₀ (γ t₀) hsrc]

/-- **The chart Jacobi expression is chart-independent.**  `chartCovDeriv` of the coordinate function
of a global section `Z` (a section of the tangent bundle agreeing with `∇_{γ'}J`), plus the
coordinate curvature term of a section `W` agreeing with `J`, gives the same tangent vector in any
two charts containing the curve.  Writing the first coordinate slot as `Z` (the *intrinsic* first
covariant derivative, not the chart one) is what makes the statement assumption-light.

This is the missing lemma of Roadmap §95.3: the chart Jacobi equation
`y'' + Γ(y')(w) + R(y,w)w = 0` is a chart-independent condition on the pair of fields. -/
theorem frameVector_chartJacobi_eq_of_charts
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {W Z : Π x : M, TangentSpace I x} (hWsm : CMDiff ∞ (T% W)) (hZsm : CMDiff ∞ (T% Z))
    {γ : ℝ → M} {t₀ : ℝ} (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    {x₀ x₁ : M} (hsrc₀ : γ t₀ ∈ (chartAt H x₀).source)
    (hsrc₁ : γ t₀ ∈ (chartAt H x₁).source)
    (hsrcEv₀ : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₀).source)
    (hsrcEv₁ : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₁).source)
    {u₀ w₀ u₁ w₁ : ℝ → E}
    (huTgt₀ : ∀ᶠ s in 𝓝 t₀, u₀ s ∈ (extChartAt I x₀).target)
    (huTgt₁ : ∀ᶠ s in 𝓝 t₀, u₁ s ∈ (extChartAt I x₁).target)
    (hγ₀ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₀).symm (u₀ s))
    (hγ₁ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₁).symm (u₁ s))
    (hu₀ : ∀ᶠ s in 𝓝 t₀, HasDerivAt u₀ (w₀ s) s)
    (hu₁ : ∀ᶠ s in 𝓝 t₀, HasDerivAt u₁ (w₁ s) s) :
    frameVector (I := I) x₀ (γ t₀)
        (chartCovDeriv cov x₀ u₀ w₀ (fun s => coordFun x₀ Z (γ s)) t₀
          + chartCurv cov x₀ (γ t₀) (coordFun x₀ W (γ t₀)) (w₀ t₀))
      = frameVector (I := I) x₁ (γ t₀)
        (chartCovDeriv cov x₁ u₁ w₁ (fun s => coordFun x₁ Z (γ s)) t₀
          + chartCurv cov x₁ (γ t₀) (coordFun x₁ W (γ t₀)) (w₁ t₀)) := by
  rw [frameVector_add, frameVector_add]
  congr 1
  · exact chartCovDeriv_coordFun_eq_of_charts (cov := cov) hZsm hγmd hsrc₀ hsrc₁ hsrcEv₀
      hsrcEv₁ huTgt₀ huTgt₁ hγ₀ hγ₁ hu₀ hu₁
  · refine frameVector_chartCurv_eq_of_charts (cov := cov) htor hsrc₀ hsrc₁ ?_ ?_
    · rw [frameVector_coordFun_eq (x₀ := x₀) hsrc₀, frameVector_coordFun_eq (x₀ := x₁) hsrc₁]
    · rw [frameVector_chartVel_eq_curveVelocity hsrc₀ huTgt₀ hγ₀ hu₀ hγmd,
        frameVector_chartVel_eq_curveVelocity hsrc₁ huTgt₁ hγ₁ hu₁ hγmd]

/-- **Chart-independence of the Jacobi equation** (usable form): if the chart Jacobi expression
vanishes in one chart containing the curve then it vanishes in any other. -/
theorem chartJacobiEquation_of_charts
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {W Z : Π x : M, TangentSpace I x} (hWsm : CMDiff ∞ (T% W)) (hZsm : CMDiff ∞ (T% Z))
    {γ : ℝ → M} {t₀ : ℝ} (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀)
    {x₀ x₁ : M} (hsrc₀ : γ t₀ ∈ (chartAt H x₀).source)
    (hsrc₁ : γ t₀ ∈ (chartAt H x₁).source)
    (hsrcEv₀ : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₀).source)
    (hsrcEv₁ : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₁).source)
    {u₀ w₀ u₁ w₁ : ℝ → E}
    (huTgt₀ : ∀ᶠ s in 𝓝 t₀, u₀ s ∈ (extChartAt I x₀).target)
    (huTgt₁ : ∀ᶠ s in 𝓝 t₀, u₁ s ∈ (extChartAt I x₁).target)
    (hγ₀ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₀).symm (u₀ s))
    (hγ₁ : γ =ᶠ[𝓝 t₀] fun s => (extChartAt I x₁).symm (u₁ s))
    (hu₀ : ∀ᶠ s in 𝓝 t₀, HasDerivAt u₀ (w₀ s) s)
    (hu₁ : ∀ᶠ s in 𝓝 t₀, HasDerivAt u₁ (w₁ s) s)
    (h₁ : chartCovDeriv cov x₁ u₁ w₁ (fun s => coordFun x₁ Z (γ s)) t₀
      + chartCurv cov x₁ (γ t₀) (coordFun x₁ W (γ t₀)) (w₁ t₀) = 0) :
    chartCovDeriv cov x₀ u₀ w₀ (fun s => coordFun x₀ Z (γ s)) t₀
      + chartCurv cov x₀ (γ t₀) (coordFun x₀ W (γ t₀)) (w₀ t₀) = 0 := by
  have h := frameVector_chartJacobi_eq_of_charts (cov := cov) htor hWsm hZsm hγmd hsrc₀ hsrc₁
    hsrcEv₀ hsrcEv₁ huTgt₀ huTgt₁ hγ₀ hγ₁ hu₀ hu₁
  have h2 : frameVector (I := I) x₀ (γ t₀)
      (chartCovDeriv cov x₀ u₀ w₀ (fun s => coordFun x₀ Z (γ s)) t₀
        + chartCurv cov x₀ (γ t₀) (coordFun x₀ W (γ t₀)) (w₀ t₀)) = 0 := by
    rw [h, h₁]
    exact map_zero _
  have h3 := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀)) h2
  rwa [GlobalBM.continuousLinearMapAt_frameVector (I := I) x₀ (γ t₀) hsrc₀, map_zero] at h3

end

end Submission.ChartIndep
