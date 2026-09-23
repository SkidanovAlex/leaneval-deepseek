import Submission.ConjPoint
import Submission.JacobiTensor

/-!
# Rauch's theorem for chart geodesics of arbitrary constant speed

The chart-local Rauch theorem `Submission.ConjPoint.eqOn_zero_of_jacobi` is stated for a
**unit-speed** chart geodesic.  The Klingenberg/Cheeger–Ebin analysis of the cut locus needs the
same statement for a chart geodesic of arbitrary constant speed `c` (the Riemannian length of the
segment of the geodesic is then `c` times the parameter length), with the conjugate-time bound
`π/(2c)` replacing `π/2`.

The Rauch *inequality* (`Submission.Rauch.rauch_inequality_speed`) and its Sturm-ready form
(`Submission.ConjPoint.rauch_sturm_ready_speed`) already carry the speed parameter `c²`; this file
assembles them into

* `eqOn_zero_Icc_of_pos_speed`: no-interior-zero case with `b - a < π/(2c)`;
* `jacobiTensor_injective_speed`: **the Jacobi tensor is injective at time `t₁` when
  `t₁ · c < π/2`** — the form in which Rauch's theorem is used for the minimal witness of the
  exponential map (`Submission.CutPoint`).

Also here: the generalisation of the "column of the Jacobi system" lemmas
(`Submission.JacobiTensor.chartCovDeriv_jacobiCol_eventuallyEq` and friends) from the fixed interval
`Ioo (-2) 2` to an arbitrary open interval `Ioo A B`, so that the hypotheses only have to be
available on the interval where the argument takes place.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.ChartBounds
open Submission.Rauch
open Submission.ConjPoint
open Submission.JacobiTensor
open Submission.BonnetMyers
open Commons.Analysis.ODE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchSpeed

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## The Jacobi system on an arbitrary interval -/

/-- The covariant derivative of a column of a solution of the Jacobi system agrees near `t` with the
corresponding column of `U` (on an arbitrary open interval `Ioo A B`). -/
lemma chartCovDeriv_jacobiCol_eventuallyEq_gen {x₀ : M} {u w : ℝ → E}
    {Y U : ℝ → E →L[ℝ] E} {e : E} {A B t : ℝ} (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    chartCovDeriv cov x₀ u w (fun s => Y s e) =ᶠ[𝓝 t] fun s => U s e := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact chartCovDeriv_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e) (hY s hs)

/-- The covariant derivative of a column of a solution of the Jacobi system is differentiable, with
derivative given by the corresponding column of `U'` (on an arbitrary open interval). -/
lemma hasDerivAt_chartCovDeriv_jacobiCol_gen {x₀ : M} {u w : ℝ → E}
    {Y U : ℝ → E →L[ℝ] E} {e : E} {A B t : ℝ} (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    HasDerivAt (chartCovDeriv cov x₀ u w (fun s => Y s e))
      (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) e) t := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq_gen (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (e := e) ht hY
  have h := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (a := e) (hU t ht)
  exact h.congr_of_eventuallyEq hev

/-- **The chart Jacobi equation for the columns of a solution of the Jacobi system** (on an
arbitrary open interval `Ioo A B`). -/
lemma jacobiEquation_col_gen {x₀ : M} {u w : ℝ → E}
    {Y U : ℝ → E →L[ℝ] E} {e : E} {A B t : ℝ} (ht : t ∈ Ioo A B)
    (hY : ∀ s ∈ Ioo A B, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) :
    chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (fun s => Y s e)) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Y t) e) (w t) = 0 := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq_gen (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (e := e) ht hY
  have hderiv : deriv (chartCovDeriv cov x₀ u w (fun s => Y s e)) t
      = (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) e) := by
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact (hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (a := e) (hU t ht)).deriv
  have hval : chartCovDeriv cov x₀ u w (fun s => Y s e) t = (U t) e := hev.eq_of_nhds
  show deriv (chartCovDeriv cov x₀ u w (fun s => Y s e)) t
      + (christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))
          (chartCovDeriv cov x₀ u w (fun s => Y s e) t)
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Y t) e) (w t) = 0
  rw [hderiv, hval]
  simp only [gammaOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply]
  rw [curvOp_apply (cov := cov) hsrc]
  abel

/-! ## Rauch's theorem with a speed parameter -/

/-- **Rauch's theorem, no-interior-zero case, with a speed parameter.**  If a Jacobi field `y` along
a chart geodesic of constant squared speed `c²` vanishes at `a` and at `b` with `b - a < π/(2c)`
and is nowhere zero in between, then it vanishes on `[a,b]`. -/
theorem eqOn_zero_Icc_of_pos_speed
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ} (hc : 0 < c)
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {a b : ℝ} (ha2 : -2 < a) (hb2 : b < 2) (hab : a < b) (habπ : b - a < Real.pi / (2 * c))
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hcont : ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc a b))
    (hya : y a = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
    (hyb : y b = 0) :
    ∀ t ∈ Icc a b, y t = 0 := by
  obtain ⟨g1, g2, hg1, hg2, hineq⟩ := rauch_sturm_ready_speed (cov := cov) (c := c)
    hcov hmet hpinch htor h hspeed ha2 hb2 hy hDy hjac hpos
  have hsqrt4 : Real.sqrt (4 * c ^ 2) = 2 * c := by
    rw [show (4 : ℝ) * c ^ 2 = (2 * c) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsqrt_a : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u a)) (y a) (y a))
      = 0 := by
    rw [hya, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero]
  have hsqrt_b : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u b)) (y b) (y b))
      = 0 := by
    rw [hyb, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero]
  have hzero := sturm_eqOn_zero_Icc (lam := 4 * c ^ 2) (by positivity) hab
    (by rw [hsqrt4]; exact habπ) hcont hsqrt_a (fun t _ => Real.sqrt_nonneg _) hg1 hg2 hineq hsqrt_b
  intro t ht
  have h1 : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) = 0 :=
    hzero ht
  have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
    positivity
  have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp h1) hGnn
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha2], by linarith [ht.2, hb2]⟩
  exact (chartGram_self_eq_zero_iff (mem_source_chartCurve (I := I) (h.2.2.1 t ht2)) (y t)).mp h2

/-- **Injectivity of the Jacobi tensor for a chart geodesic of constant speed** `c ≡ √⟨w,w⟩`: the
columns of the Jacobi tensor are the Jacobi fields vanishing at `0`, and none of them vanishes
again before `π/(2c)` in the parameter, i.e. before length `π/2`.

The hypotheses are the Jacobi system on an arbitrary open interval `Ioo A B` with `-2 < A < 0`,
`t₁ < B < 2`, and the constancy of the chart speed there. -/
theorem jacobiTensor_injective_speed
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ} (hc : 0 < c)
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {A B t₁ : ℝ} (hA2 : -2 < A) (hA0 : A < 0) (hBt : t₁ < B) (hB2 : B < 2)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Ioo A B,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    (ht₁pos : 0 < t₁) (ht₁π : t₁ * c < Real.pi / 2) :
    Function.Injective (Y t₁) := by
  have hspeed' : ∀ t ∈ Ioo A B,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2 :=
    fun t ht => hspeed t ⟨by linarith [ht.1, hA2], by linarith [ht.2, hB2]⟩
  have h0mem : (0 : ℝ) ∈ Ioo A B := ⟨hA0, by linarith⟩
  intro z₁ z₂ hz
  set e : E := z₁ - z₂ with hedef
  set y : ℝ → E := fun s => Y s e with hydef
  have hy0 : y 0 = 0 := by simp only [hydef, hY0, ContinuousLinearMap.zero_apply]
  have hyt : y t₁ = 0 := by simp only [hydef, hedef, map_sub, hz, sub_self]
  -- the derivative of `y` at `0` is `e`
  have hderiv0 : HasDerivAt y e 0 := by
    have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e) (hY 0 h0mem)
    have hd0 : (U 0) e - (gammaOp (cov := cov) x₀ u w 0) ((Y 0) e) = e := by
      rw [hY0, hU0]
      simp
    exact hh.congr_deriv hd0
  -- the field and its covariant derivative are differentiable on `(0,t₁)`
  have hy : ∀ t ∈ Ioo 0 t₁, HasDerivAt y (deriv y t) t := by
    intro t ht
    have hmem : t ∈ Ioo A B := ⟨by linarith [ht.1], by linarith [ht.2, hBt]⟩
    have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e) (hY t hmem)
    simpa only [hydef] using hh.congr_deriv hh.deriv.symm
  have hDy : ∀ t ∈ Ioo 0 t₁, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t := by
    intro t ht
    have hmem : t ∈ Ioo A B := ⟨by linarith [ht.1], by linarith [ht.2, hBt]⟩
    have hh := hasDerivAt_chartCovDeriv_jacobiCol_gen (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (e := e) hmem hY hU
    simpa only [hydef] using hh.congr_deriv hh.deriv.symm
  have hjac : ∀ t ∈ Ioo 0 t₁, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0 := by
    intro t ht
    have hmem : t ∈ Ioo A B := ⟨by linarith [ht.1], by linarith [ht.2, hBt]⟩
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hmem.1, hA2], by linarith [hmem.2, hB2]⟩
    simpa only [hydef] using jacobiEquation_col_gen (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (e := e) hmem hY hU (mem_source_chartCurve (I := I) (h.2.2.1 t ht2))
  -- continuity of the field and the covariant-derivative data on `Icc 0 T`
  have hcont : ∀ {T : ℝ}, T ≤ t₁ → ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc 0 T) := by
    intro T hTle
    have hmem1 : ∀ t ∈ Icc (0:ℝ) T, t ∈ Ioo A B := fun t ht =>
      ⟨by linarith [ht.1, hA0], by linarith [ht.2, hTle, hBt]⟩
    have hmem2 : ∀ t ∈ Icc (0:ℝ) T, t ∈ Ioo (-2 : ℝ) 2 := fun t ht =>
      ⟨by linarith [(hmem1 t ht).1, hA2], by linarith [(hmem1 t ht).2, hB2]⟩
    have hycont : ContinuousOn y (Icc 0 T) := fun t ht =>
      ((hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e)
        (hY t (hmem1 t ht))).continuousAt).continuousWithinAt
    have hucont : ContinuousOn u (Icc 0 T) := fun t ht =>
      ((h.2.2.2.1 t (hmem2 t ht)).continuousAt).continuousWithinAt
    have hgc := continuousOn_chartGram_curve (I := I) (x₀ := x₀)
      (continuousOn_chartCurve hucont (fun t ht => h.2.2.1 t (hmem2 t ht))) hycont hycont
      (fun t ht => mem_source_chartCurve (I := I) (h.2.2.1 t (hmem2 t ht)))
    exact Real.continuous_sqrt.comp_continuousOn hgc
  -- the field is nonzero immediately to the right of `0` when `e ≠ 0`
  by_cases he : e = 0
  · rw [hedef] at he
    exact sub_eq_zero.mp he
  · obtain ⟨δ, hδpos, hδne⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, y t ≠ 0 := by
      have hslope : Tendsto (fun t : ℝ => t⁻¹ • (y t - y 0)) (𝓝[>] (0 : ℝ)) (𝓝 e) := by
        simpa only [zero_add] using hderiv0.tendsto_slope_zero_right
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (y t - y 0) ≠ 0 := hslope.eventually_ne he
      have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ≠ 0 := by
        filter_upwards [hev] with t ht hyt
        exact ht (by rw [hyt, hy0, sub_self, smul_zero])
      obtain ⟨d, hd, hdsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev'
      exact ⟨d, hd, fun t ht => hdsub ht⟩
    -- the first zero of `y` in `(0,t₁]`
    have hkey : ∃ T : ℝ, 0 < T ∧ T ≤ t₁ ∧ y T = 0 ∧ ∀ s ∈ Ioo 0 T, y s ≠ 0 := by
      by_cases hcase : ∃ s ∈ Ioo (0:ℝ) t₁, y s = 0
      · obtain ⟨s₀, hs₀, hy₀⟩ := hcase
        set S : Set ℝ := {s | s ∈ Ioo (0:ℝ) t₁ ∧ y s = 0} with hSdef
        have hSne : S.Nonempty := ⟨s₀, by rw [hSdef]; exact ⟨hs₀, hy₀⟩⟩
        have hSbdd : BddBelow S := ⟨0, fun s hs => by rw [hSdef] at hs; exact hs.1.1.le⟩
        set T : ℝ := sInf S with hTdef
        have hTinf : T ≤ s₀ := csInf_le hSbdd (by rw [hSdef]; exact ⟨hs₀, hy₀⟩)
        have hTlt : T < t₁ := lt_of_le_of_lt hTinf hs₀.2
        have hTle : T ≤ t₁ := hTlt.le
        have hTpos : 0 < T := by
          have hle : δ ≤ T := le_csInf hSne (fun s hs => by
            rw [hSdef] at hs
            by_contra hcon
            push Not at hcon
            exact hδne s ⟨hs.1.1, hcon⟩ hs.2)
          linarith
        have hTmem : T ∈ Ioo (0:ℝ) t₁ := ⟨hTpos, hTlt⟩
        have hyT : y T = 0 := by
          by_contra hne
          have hcT : ContinuousAt y T := (hy T hTmem).continuousAt
          have hnb : {s : ℝ | y s ≠ 0} ∈ 𝓝 T := hcT (isOpen_ne.mem_nhds hne)
          rw [Metric.mem_nhds_iff] at hnb
          obtain ⟨ε, hε, hεS⟩ := hnb
          obtain ⟨s, hsS, hTs⟩ := exists_lt_of_csInf_lt hSne (show T < T + ε by linarith)
          have hle : T ≤ s := csInf_le hSbdd hsS
          rw [hSdef] at hsS
          have hlt : dist s T < ε := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith
          exact hεS hlt hsS.2
        refine ⟨T, hTpos, hTle, hyT, fun s hs hys => ?_⟩
        have hsS : s ∈ S := by rw [hSdef]; exact ⟨⟨hs.1, lt_of_lt_of_le hs.2 hTle⟩, hys⟩
        have := csInf_le hSbdd hsS
        exact absurd hs.2 (not_lt.mpr this)
      · push Not at hcase
        exact ⟨t₁, ht₁pos, le_rfl, hyt,
          fun s hs => hcase s ⟨hs.1, lt_of_lt_of_le hs.2 le_rfl⟩⟩
    obtain ⟨T, hTpos, hTle, hyT, hTne⟩ := hkey
    -- apply the no-interior-zero case on `[0,T]`
    have hTb2 : T < 2 := by linarith [hTle, hBt, hB2]
    have habπ : T - 0 < Real.pi / (2 * c) := by
      have h1 : T * c < Real.pi / 2 :=
        calc T * c ≤ t₁ * c := mul_le_mul_of_nonneg_right hTle hc.le
          _ < Real.pi / 2 := ht₁π
      rw [sub_zero, lt_div_iff₀ (by positivity : (0:ℝ) < 2 * c)]
      linarith
    have hpos : ∀ t ∈ Ioo (0:ℝ) T,
        0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
      intro t ht
      have htne : y t ≠ 0 := hTne t ht
      have hmem : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2, hTb2]⟩
      have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
        mem_source_chartCurve (I := I) (h.2.2.1 t hmem)
      have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
        rw [chartGram_apply, real_inner_self_eq_norm_sq]
        positivity
      exact lt_of_le_of_ne hGnn
        (fun h0 => htne ((chartGram_self_eq_zero_iff hsrc (y t)).mp h0.symm))
    have hzero := eqOn_zero_Icc_of_pos_speed (cov := cov) (c := c)
      (hcov := ‹ContMDiffCovariantDerivative cov ∞›) hmet hpinch htor h hc hspeed
      (by norm_num : (-2:ℝ) < 0) hTb2 hTpos habπ
      (fun t ht => hy t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩)
      (fun t ht => hDy t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩)
      (fun t ht => hjac t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩)
      (hcont (T := T) hTle) hy0 hpos hyT
    -- contradict the non-vanishing near `0`
    set t' : ℝ := min δ T / 2 with ht'def
    have ht'pos : 0 < t' := by rw [ht'def]; positivity
    have ht'δ : t' < δ := by
      have h1 : min δ T ≤ δ := min_le_left _ _
      rw [ht'def]; linarith
    have ht'T : t' < T := by
      have h1 : min δ T ≤ T := min_le_right _ _
      rw [ht'def]; linarith
    exact absurd (hzero t' ⟨ht'pos.le, ht'T.le⟩) (hδne t' ⟨ht'pos, ht'δ⟩)

end

end Submission.RauchSpeed
