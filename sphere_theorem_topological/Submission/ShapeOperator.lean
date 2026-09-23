import Submission.JacobiTensor
import Submission.CurvatureSym

/-!
# The shape operator of the Jacobi tensor

For a unit-speed chart geodesic with Jacobi system `(Y, U)` (`Submission/JacobiTensor`),
`Y t` is injective for `t ∈ (0, π/2)` (`JacobiTensor.jacobiTensor_injective`), hence invertible,
and we define the **shape operator** `Ŝ t = U t ∘ (Y t)⁻¹`.

The two structural results of this file, which are the heart of the Riccati form of Rauch's
comparison theorem, are

* `wronskian_eq_zero`: for all `a b : E` and `t` in the interval,
  `chartGram (U t a) (Y t b) = chartGram (Y t a) (U t b)`;
* `shapeOp_self_adjoint`: `Ŝ t` is self-adjoint for the chart metric at `γ t`.

Both follow from the Wronskian identity `d/dt (⟨U a, Y b⟩ - ⟨Y a, U b⟩) = 0`, whose derivative
vanishes by `CurvatureSym.chartCurv_self_adjoint`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.ChartBounds
open Submission.JacobiVec
open Submission.BonnetMyers
open Submission.JacobiTensor
open Submission.CurvatureSym
open Submission.Gauss

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ShapeOperator

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
  {x₀ : M} {v : E} {u w : ℝ → E}

/-! ## The Wronskian identity -/

/-- The covariant derivative of `s ↦ U s a` (constant `a`) is `-Rop (Y t a)`. -/
lemma chartCovDeriv_U_const {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hU : HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    chartCovDeriv cov x₀ u w (fun s => U s a) t
      = -((curvOp (cov := cov) x₀ u w t) ((Y t) a)) := by
  have h := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) hU
  simp only [chartCovDeriv]
  rw [h.deriv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, gammaOp]
  abel

/-- **The Wronskian identity.**  Along a unit-speed chart geodesic with Jacobi system `(Y, U)`,
for all vectors `a b : E` and all `t` in the interval,
`⟨U t a, Y t b⟩ = ⟨Y t a, U t b⟩`. -/
theorem wronskian_eq_zero (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (h : HasChartGeodesic cov x₀ v u w)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    {a b : E} {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((U t) a) ((Y t) b)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) ((U t) b) := by
  set F : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((U s) a)
    ((Y s) b) - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((Y s) a) ((U s) b)
    with hFdef
  have hderiv : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt F 0 s := by
    intro s hs
    have hutgt : u s ∈ (extChartAt I x₀).target := h.2.2.1 s hs
    have hstay : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr => h.2.2.1 r hr
    have hUa : HasDerivAt (fun r => U r a) (deriv (fun r => U r a) s) s := by
      have hh := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := a) (hU s hs)
      rw [hh.deriv]; exact hh
    have hYb : HasDerivAt (fun r => Y r b) (deriv (fun r => Y r b) s) s := by
      have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := b)
        (hY s hs)
      rw [hh.deriv]; exact hh
    have hYa : HasDerivAt (fun r => Y r a) (deriv (fun r => Y r a) s) s := by
      have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a)
        (hY s hs)
      rw [hh.deriv]; exact hh
    have hUb : HasDerivAt (fun r => U r b) (deriv (fun r => U r b) s) s := by
      have hh := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
        (a := b) (hU s hs)
      rw [hh.deriv]; exact hh
    have h1 := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
      (h.2.2.2.1 s hs) hutgt hstay hUa hYb
    have h2 := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
      (h.2.2.2.1 s hs) hutgt hstay hYa hUb
    have hmain := h1.sub h2
    have hD1 : chartCovDeriv cov x₀ u w (fun r => U r a) s
        = -((curvOp (cov := cov) x₀ u w s) ((Y s) a)) :=
      chartCovDeriv_U_const (cov := cov) (x₀ := x₀) (u := u) (w := w) (hU s hs)
    have hD2 : chartCovDeriv cov x₀ u w (fun r => Y r b) s = (U s) b :=
      chartCovDeriv_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := b) (hY s hs)
    have hD3 : chartCovDeriv cov x₀ u w (fun r => Y r a) s = (U s) a :=
      chartCovDeriv_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) (hY s hs)
    have hD4 : chartCovDeriv cov x₀ u w (fun r => U r b) s
        = -((curvOp (cov := cov) x₀ u w s) ((Y s) b)) :=
      chartCovDeriv_U_const (cov := cov) (x₀ := x₀) (u := u) (w := w) (hU s hs)
    rw [hD1, hD2, hD3, hD4] at hmain
    have hadj : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        ((curvOp (cov := cov) x₀ u w s) ((Y s) a)) ((Y s) b)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((Y s) a)
            ((curvOp (cov := cov) x₀ u w s) ((Y s) b)) := by
      rw [curvOp_apply (cov := cov) (mem_source_chartCurve (I := I) hutgt),
        curvOp_apply (cov := cov) (mem_source_chartCurve (I := I) hutgt)]
      exact chartCurv_self_adjoint (cov := cov) (hcov := ‹ContMDiffCovariantDerivative cov ∞›)
        htor hmet x₀ (mem_source_chartCurve (I := I) hutgt) ((Y s) a) (w s) ((Y s) b)
    have hval0 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (-((curvOp (cov := cov) x₀ u w s) ((Y s) a))) ((Y s) b)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((U s) a) ((U s) b)
        - (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((U s) a) ((U s) b)
          + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((Y s) a)
              (-((curvOp (cov := cov) x₀ u w s) ((Y s) b)))) = 0 := by
      have hneg_snd : ∀ x : E, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          ((Y s) a) (-x)
          = -chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) ((Y s) a) x := by
        intro x
        rw [chartGram_comm, chartGram_neg_fst, chartGram_comm]
      rw [chartGram_neg_fst, hneg_snd, hadj]
      ring
    exact hmain.congr_deriv hval0
  have hsub : ∀ x ∈ Icc (min 0 t) (max 0 t), x ∈ Ioo (-2 : ℝ) 2 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min (by norm_num) ht.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt (by norm_num) ht.2)⟩
  have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc min_le_max
    (fun x hx => hderiv x (hsub x hx))
  have hFt : F t = F (min 0 t) := hconst t ⟨min_le_right _ _, le_max_right _ _⟩
  have hF0 : F 0 = F (min 0 t) := hconst 0 ⟨min_le_left _ _, le_max_left _ _⟩
  have hFz : F 0 = 0 := by
    simp only [hFdef, hY0, hU0, ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply]
    rw [chartGram_zero_snd, chartGram_zero_fst]
    ring
  have hFt0 : F t = 0 := by rw [hFt, ← hF0]; exact hFz
  exact sub_eq_zero.mp hFt0

/-! ## The shape operator and its self-adjointness -/

section ShapeOp

variable (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
  (h : HasChartGeodesic cov x₀ v u w)
  (hunit : ∀ t ∈ Ioo (-2 : ℝ) 2,
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
  {Y U : ℝ → E →L[ℝ] E}
  (hY : ∀ t ∈ Ioo (-2 : ℝ) 2,
    HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
  (hU : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
    - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
  (hY0 : Y 0 = 0) (hU0 : U 0 = 1)

include htor hmet hpinch h hunit hY hU hY0 hU0

/-- `Y t` is injective for `t ∈ (0, π/2)`. -/
theorem Y_injective_of_mem {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    Function.Injective (Y t) :=
  jacobiTensor_injective (cov := cov) htor hmet hpinch h hunit hY hU hY0 hU0 ht.1 ht.2

/-- The Jacobi tensor viewed as a linear equivalence, for `t ∈ (0, π/2)`. -/
noncomputable def Yequiv (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi / 2)) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective ((Y t).toLinearMap)
    ⟨Y_injective_of_mem htor hmet hpinch h hunit hY hU hY0 hU0 ht,
      (LinearMap.injective_iff_surjective (f := (Y t).toLinearMap)).mp
        (Y_injective_of_mem htor hmet hpinch h hunit hY hU hY0 hU0 ht)⟩

/-- The inverse of the Jacobi tensor at times `t ∈ (0, π/2)`. -/
noncomputable def Yinv (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi / 2)) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) ((Yequiv htor hmet hpinch h hunit hY hU hY0 hU0 t ht).symm :
    E →ₗ[ℝ] E)

lemma Y_apply_Yinv {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (x : E) :
    Y t (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht x) = x := by
  exact LinearEquiv.apply_symm_apply (Yequiv htor hmet hpinch h hunit hY hU hY0 hU0 t ht) x

/-- The **shape operator** `Ŝ = U ∘ Y⁻¹` of the Jacobi tensor. -/
noncomputable def shapeOp (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi / 2)) : E →L[ℝ] E :=
  (U t).comp (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht)

lemma shapeOp_apply {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (x : E) :
    shapeOp htor hmet hpinch h hunit hY hU hY0 hU0 t ht x
      = (U t) (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht x) :=
  rfl

/-- **Self-adjointness of the shape operator**: `⟨Ŝ u, v⟩ = ⟨u, Ŝ v⟩` for the chart metric at
`γ t`. -/
theorem shapeOp_self_adjoint {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (x y : E) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (shapeOp htor hmet hpinch h hunit hY hU hY0 hU0 t ht x) y
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) x
        (shapeOp htor hmet hpinch h hunit hY hU hY0 hU0 t ht y) := by
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_lt_four]⟩
  have hx := Y_apply_Yinv htor hmet hpinch h hunit hY hU hY0 hU0 ht x
  have hy := Y_apply_Yinv htor hmet hpinch h hunit hY hU hY0 hU0 ht y
  have hw := wronskian_eq_zero (cov := cov) htor hmet h hY hU hY0 hU0
    (a := Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht x)
    (b := Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht y) ht2
  rw [hx, hy] at hw
  simp only [shapeOp, ContinuousLinearMap.comp_apply]
  exact hw

/-- `Yinv` is a left inverse of `Y`. -/
lemma Yinv_comp_Y {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht).comp (Y t) = 1 := by
  ext x
  exact LinearEquiv.symm_apply_apply (Yequiv htor hmet hpinch h hunit hY hU hY0 hU0 t ht) x

lemma Yinv_apply_Y {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) (x : E) :
    Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht (Y t x) = x := by
  have h : (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht).comp (Y t) = 1 :=
    Yinv_comp_Y htor hmet hpinch h hunit hY hU hY0 hU0 ht
  exact congrFun (congrArg DFunLike.coe h) x

/-- **The difference formula for the inverse**: for `s, t ∈ (0, π/2)`,
`Yinv s - Yinv t = - Yinv s ∘ (Y s - Y t) ∘ Yinv t`.

This is the algebraic input for differentiating `t ↦ (Y t)⁻¹` (the standard "inverse is
differentiable" computation). -/
theorem Yinv_sub {s t : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    Yinv htor hmet hpinch h hunit hY hU hY0 hU0 s hs - Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht
      = - (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 s hs).comp
          ((Y s - Y t).comp (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht)) := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  have h1 : Y t (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht x) = x :=
    Y_apply_Yinv htor hmet hpinch h hunit hY hU hY0 hU0 ht x
  have h2 : Yinv htor hmet hpinch h hunit hY hU hY0 hU0 s hs
      (Y s (Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht x))
      = Yinv htor hmet hpinch h hunit hY hU hY0 hU0 t ht x :=
    Yinv_apply_Y htor hmet hpinch h hunit hY hU hY0 hU0 hs _
  rw [h1, h2]
  abel

end ShapeOp

end

end Submission.ShapeOperator
