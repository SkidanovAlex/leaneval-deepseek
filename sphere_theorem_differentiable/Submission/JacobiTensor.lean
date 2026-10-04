import Submission.BonnetMyers
import Submission.JacobiVec

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Jacobi tensor along a chart geodesic

This file sets up the objects needed for the **operator (Ricatti) form** of Rauch's comparison
theorem in a chart:

* `gammaOp x₀ u w t`, the Christoffel operator `a ↦ Γ(γ(t))(a, γ'(t))` along the chart geodesic;
* `curvOp x₀ u w t`, the **coordinate curvature operator** `a ↦ chartCurv a (γ'(t))` (the
  `R(·,γ')γ'` operator of the Jacobi equation), with
  `curvOp_apply : curvOp t a = chartCurv cov x₀ (γ t) a (w t)`;
* their continuity along the geodesic (`continuousOn_gammaOp`, `continuousOn_curvOp`), which is
  what the ODE existence theorems need.

`curvOp` is built as a finite sum so that it is a *continuous* linear map by construction; the
identification with `chartCurv` uses the linearity of `chartCurv` in its first argument
(`Submission/JacobiVec`).
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

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.JacobiTensor

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The Christoffel operator along the geodesic -/

/-- The Christoffel operator along the chart curve: `Γ̂(t) a = Γ(γ(t))(a, γ'(t))`. -/
noncomputable def gammaOp (x₀ : M) (u w : ℝ → E) (t : ℝ) : E →L[ℝ] E :=
  christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
    (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))

lemma gammaOp_apply {x₀ : M} {u w : ℝ → E} {t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) (a : E) :
    gammaOp (cov := cov) x₀ u w t a
      = christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) :=
  christoffelLM_apply (cov := cov) hsrc a

/-- Continuity of the Christoffel operator along a chart geodesic. -/
lemma continuousOn_gammaOp [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ContinuousOn (gammaOp (cov := cov) x₀ u w) (Ioo (-2 : ℝ) 2) :=
  continuousOn_christoffelLM_along (cov := cov) htor h

/-! ## Linearity of `chartCurv` in its first slot over finite sums -/

lemma chartCurv_zero_fst [ContMDiffCovariantDerivative cov ∞] (x₀ p : M)
    (hp : p ∈ (chartAt H x₀).source) (Y : E) :
    chartCurv cov x₀ p 0 Y = 0 := by
  have h := chartCurv_smul_fst (cov := cov) x₀ p hp (0 : ℝ) (0 : E) Y
  simpa using h

lemma chartCurv_sum_fst [ContMDiffCovariantDerivative cov ∞] {ι : Type*}
    (s : Finset ι) (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (c : ι → ℝ) (X : ι → E)
    (Y : E) :
    chartCurv cov x₀ p (∑ i ∈ s, c i • X i) Y = ∑ i ∈ s, c i • chartCurv cov x₀ p (X i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact chartCurv_zero_fst (cov := cov) x₀ p hp Y
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        chartCurv_add_fst (cov := cov) x₀ p hp,
        chartCurv_smul_fst (cov := cov) x₀ p hp, ih]

/-! ## Continuity of `chartCurv` along a curve -/

/-- Continuity of the chart curvature term along a continuous curve. -/
lemma continuousOn_chartCurv_curve [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {γ : ℝ → M}
    {X Y : ℝ → E} {B : Set ℝ} (hγ : ContinuousOn γ B) (hX : ContinuousOn X B)
    (hY : ContinuousOn Y B) (hmem : ∀ t ∈ B, γ t ∈ (chartAt H x₀).source) :
    ContinuousOn (fun t : ℝ => chartCurv cov x₀ (γ t) (X t) (Y t)) B := by
  have h1 : ContinuousOn (fun t : ℝ => dB cov x₀ (γ t) (X t) (Y t) (Y t)) B :=
    continuousOn_dB_curve (cov := cov) hγ hX hY hY hmem
  have h2 : ContinuousOn (fun t : ℝ => dB cov x₀ (γ t) (Y t) (Y t) (X t)) B :=
    continuousOn_dB_curve (cov := cov) hγ hY hY hX hmem
  have h3 : ContinuousOn (fun t : ℝ =>
      chrB cov x₀ (γ t) (chrB cov x₀ (γ t) (Y t) (Y t)) (X t)) B :=
    continuousOn_chrB_curve (cov := cov) hγ
      (continuousOn_chrB_curve (cov := cov) hγ hY hY hmem) hX hmem
  have h4 : ContinuousOn (fun t : ℝ =>
      chrB cov x₀ (γ t) (chrB cov x₀ (γ t) (Y t) (X t)) (Y t)) B :=
    continuousOn_chrB_curve (cov := cov) hγ
      (continuousOn_chrB_curve (cov := cov) hγ hY hX hmem) hY hmem
  refine ((h1.sub h2).add h3).sub h4 |>.congr fun t _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, chartCurv]

/-! ## The coordinate curvature operator -/

/-- The coordinate curvature operator `a ↦ chartCurv a (γ'(t))` along the chart curve, built as a
finite sum so that it is a continuous linear map by construction. -/
noncomputable def curvOp (x₀ : M) (u w : ℝ → E) (t : ℝ) : E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
      (chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t))

lemma curvOp_apply [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u w : ℝ → E} {t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) (a : E) :
    curvOp (cov := cov) x₀ u w t a
      = chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) a (w t) := by
  rw [curvOp]
  rw [ContinuousLinearMap.sum_apply]
  have hsum : (∑ i : Fin (Module.finrank ℝ E),
        (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
          (chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t)) a)
      = ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i) a •
            chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [hsum, ← chartCurv_sum_fst (cov := cov) Finset.univ x₀ ((extChartAt I x₀).symm (u t)) hsrc
    (fun i => ((Module.finBasis ℝ E).coord i) a) (fun i => (Module.finBasis ℝ E) i) (w t)]
  congr 1
  exact (Module.finBasis ℝ E).sum_repr a

/-- Continuity of the coordinate curvature operator along the chart curve. -/
lemma continuousOn_curvOp [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u w : ℝ → E}
    {B : Set ℝ} (hu : ContinuousOn u B) (hw : ContinuousOn w B)
    (hmem : ∀ t ∈ B, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (curvOp (cov := cov) x₀ u w) B := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) B :=
    continuousOn_chartCurve hu hmem
  have hsrc : ∀ t ∈ B, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  change ContinuousOn (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E),
    (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
      (chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t))) B
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine Continuous.comp_continuousOn
    (ContinuousLinearMap.smulRightL ℝ E E
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).continuous ?_
  exact continuousOn_chartCurv_curve (cov := cov) hγ continuousOn_const hw hsrc

end

end Submission.JacobiTensor

namespace Submission.JacobiTensor

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## Continuity of the operator product -/

/-- The Cartesian product of two continuous families of continuous linear maps is continuous. -/
theorem continuous_clm_prod {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {ι : Type*} [TopologicalSpace ι] {F G : ι → X →L[ℝ] Y}
    (hF : Continuous F) (hG : Continuous G) :
    Continuous (fun p : ι => (F p).prod (G p)) := by
  have h1 : Continuous (fun p : ι => (F p).prodMap (G p)) :=
    (ContinuousLinearMap.prodMapL ℝ X Y X Y).continuous.comp (Continuous.prodMk hF hG)
  have h2 : Continuous (fun p : ι => ((ContinuousLinearMap.compL ℝ X (X × X) (Y × Y))
      ((F p).prodMap (G p)))
        ((ContinuousLinearMap.id ℝ X).prod (ContinuousLinearMap.id ℝ X))) :=
    ((ContinuousLinearMap.compL ℝ X (X × X) (Y × Y)).continuous.comp h1).clm_apply
      continuous_const
  refine h2.congr fun p => ?_
  refine ContinuousLinearMap.ext fun x => ?_
  rfl

/-! ## The first-order Jacobi system -/

/-- The assembly of the Jacobi system from the Christoffel and curvature operators. -/
noncomputable def jacobiSysAux :
    (E →L[ℝ] E) × (E →L[ℝ] E) →
      ((E →L[ℝ] E) × (E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E) × (E →L[ℝ] E)) :=
  fun p => ContinuousLinearMap.prod
    (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)
      - (ContinuousLinearMap.compL ℝ E E E p.1).comp
          (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)))
    (-((ContinuousLinearMap.compL ℝ E E E p.1).comp
        (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)))
      - (ContinuousLinearMap.compL ℝ E E E p.2).comp
          (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)))

/-- The coefficient of the first-order Jacobi system `(Y,U)' = (U - Γ̂Y, -Γ̂U - Rop Y)`. -/
noncomputable def jacobiSys (x₀ : M) (u w : ℝ → E) (t : ℝ) :
    (E →L[ℝ] E) × (E →L[ℝ] E) →L[ℝ] ((E →L[ℝ] E) × (E →L[ℝ] E)) :=
  jacobiSysAux (gammaOp (cov := cov) x₀ u w t, curvOp (cov := cov) x₀ u w t)

lemma jacobiSys_apply {x₀ : M} {u w : ℝ → E} {t : ℝ} (Z₁ Z₂ : E →L[ℝ] E) :
    jacobiSys (cov := cov) x₀ u w t (Z₁, Z₂)
      = (Z₂ - (gammaOp (cov := cov) x₀ u w t).comp Z₁,
          -((gammaOp (cov := cov) x₀ u w t).comp Z₂)
            - (curvOp (cov := cov) x₀ u w t).comp Z₁) := by
  simp only [jacobiSys, jacobiSysAux, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
  rfl

lemma continuous_jacobiSysAux :
    Continuous (jacobiSysAux (E := E)) := by
  have h1 : Continuous (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) =>
      (ContinuousLinearMap.compL ℝ E E E p.1).comp
        (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E))) := by fun_prop
  have h2 : Continuous (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) =>
      (ContinuousLinearMap.compL ℝ E E E p.1).comp
        (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E))) := by fun_prop
  have h3 : Continuous (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) =>
      (ContinuousLinearMap.compL ℝ E E E p.2).comp
        (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E))) := by fun_prop
  have h4 : Continuous (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) =>
      ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)
        - (ContinuousLinearMap.compL ℝ E E E p.1).comp
            (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E))) :=
    continuous_const.sub h1
  have h5 : Continuous (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) =>
      -((ContinuousLinearMap.compL ℝ E E E p.1).comp
          (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)))
        - (ContinuousLinearMap.compL ℝ E E E p.2).comp
            (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E))) := h2.neg.sub h3
  exact continuous_clm_prod (X := (E →L[ℝ] E) × (E →L[ℝ] E)) (Y := E →L[ℝ] E) h4 h5

lemma continuousOn_jacobiSys [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ContinuousOn (jacobiSys (cov := cov) x₀ u w) (Ioo (-2 : ℝ) 2) := by
  have hG : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Ioo (-2 : ℝ) 2) :=
    continuousOn_gammaOp (cov := cov) htor h
  have hw : ContinuousOn w (Ioo (-2 : ℝ) 2) :=
    HasDerivAt.continuousOn fun t ht => h.2.2.2.2 t ht
  have hR : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Ioo (-2 : ℝ) 2) :=
    continuousOn_curvOp (cov := cov) (HasDerivAt.continuousOn fun t ht => h.2.2.2.1 t ht)
      hw (fun t ht => h.2.2.1 t ht)
  have hcomp := (continuous_jacobiSysAux (E := E)).comp_continuousOn (hG.prodMk hR)
  refine hcomp.congr fun t _ => ?_
  rfl

/-- **Existence of the Jacobi tensor.**  On `Icc a b ⊆ Ioo (-2) 2` containing `0` there are
`Y, U : ℝ → E →L[ℝ] E` with `Y 0 = 0`, `U 0 = 1` and
`Y' = U - Γ̂ ∘ Y`,  `U' = -Γ̂ ∘ U - Rop ∘ Y`. -/
theorem exists_jacobiSystem [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {a b : ℝ} (hab : a < b) (habt : Icc a b ⊆ Ioo (-2 : ℝ) 2) (h0 : (0 : ℝ) ∈ Icc a b) :
    ∃ Y U : ℝ → E →L[ℝ] E, Y 0 = 0 ∧ U 0 = 1 ∧
      (∀ t ∈ Icc a b, HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
      (∀ t ∈ Icc a b, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  have hc : ContinuousOn (jacobiSys (cov := cov) x₀ u w) (Icc a b) :=
    (continuousOn_jacobiSys (cov := cov) htor h).mono habt
  obtain ⟨Z, hZ0, hZode, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc
      (E := (E →L[ℝ] E) × (E →L[ℝ] E)) hab hc h0
      ((0 : E →L[ℝ] E), (1 : E →L[ℝ] E))
  refine ⟨fun t => (Z t).1, fun t => (Z t).2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hZ0
  · simpa using congrArg Prod.snd hZ0
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).1)
        ((jacobiSys (cov := cov) x₀ u w t (Z t)).1) t := (hZode t ht).fst
    rw [jacobiSys_apply] at h1
    exact h1
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).2)
        ((jacobiSys (cov := cov) x₀ u w t (Z t)).2) t := (hZode t ht).snd
    rw [jacobiSys_apply] at h1
    exact h1

end

end Submission.JacobiTensor

namespace Submission.JacobiTensor

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
  {x₀ : M} {v : E} {u w : ℝ → E}

/-! ## The columns of the Jacobi tensor are Jacobi fields -/

/-- The derivative of a column of a solution of the Jacobi system. -/
lemma hasDerivAt_jacobiCol {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hY : HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    HasDerivAt (fun s => Y s a) ((U t) a - (gammaOp (cov := cov) x₀ u w t) ((Y t) a)) t := by
  have h := hY.clm_apply (hasDerivAt_const (c := a) (x := t))
  simpa using h

/-- The covariant derivative of a column of a solution of the Jacobi system is the corresponding
column of `U`. -/
lemma chartCovDeriv_jacobiCol {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hY : HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    chartCovDeriv cov x₀ u w (fun s => Y s a) t = (U t) a := by
  have h := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) hY
  simp only [chartCovDeriv]
  rw [h.deriv]
  simp only [gammaOp]
  abel

/-- The covariant derivative of a column, as a function, agrees near `t` with the corresponding
column of `U`. -/
lemma chartCovDeriv_jacobiCol_eventuallyEq {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (ht : t ∈ Ioo (-2 : ℝ) 2)
    (hY : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    chartCovDeriv cov x₀ u w (fun s => Y s a) =ᶠ[𝓝 t] (fun s => U s a) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact chartCovDeriv_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := a) (hY s hs)

/-- The derivative of the covariant derivative of a column. -/
lemma hasDerivAt_jacobiCol_covDeriv {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (hU : HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) :
    HasDerivAt (fun s => U s a)
      (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) t := by
  have h := hU.clm_apply (hasDerivAt_const (c := a) (x := t))
  simpa using h

/-- The covariant derivative of a column is differentiable with derivative given by `U' a`. -/
lemma hasDerivAt_chartCovDeriv_jacobiCol {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (ht : t ∈ Ioo (-2 : ℝ) 2)
    (hY : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s) :
    HasDerivAt (chartCovDeriv cov x₀ u w (fun s => Y s a))
      (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) t := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (a := a) ht hY
  have h := hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (a := a) (hU t ht)
  exact h.congr_of_eventuallyEq hev

/-- **The chart Jacobi equation for the columns of a solution of the Jacobi system.** -/
lemma jacobiEquation_col {Y U : ℝ → E →L[ℝ] E} {a : E} {t : ℝ}
    (ht : t ∈ Ioo (-2 : ℝ) 2)
    (hY : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt Y (U s - (gammaOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hU : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w s).comp (U s))
      - (curvOp (cov := cov) x₀ u w s).comp (Y s)) s)
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) :
    chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (fun s => Y s a)) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t) = 0 := by
  have hev := chartCovDeriv_jacobiCol_eventuallyEq (cov := cov) (x₀ := x₀) (u := u) (w := w)
    (Y := Y) (U := U) (a := a) ht hY
  have hderiv : deriv (chartCovDeriv cov x₀ u w (fun s => Y s a)) t
      = (((-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t))) a) := by
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact (hasDerivAt_jacobiCol_covDeriv (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (a := a) (hU t ht)).deriv
  have hval : chartCovDeriv cov x₀ u w (fun s => Y s a) t = (U t) a := hev.eq_of_nhds
  show deriv (chartCovDeriv cov x₀ u w (fun s => Y s a)) t
      + (christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))
          (chartCovDeriv cov x₀ u w (fun s => Y s a) t)
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Y t) a) (w t) = 0
  rw [hderiv, hval]
  simp only [gammaOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply]
  rw [curvOp_apply (cov := cov) hsrc]
  abel

end

end Submission.JacobiTensor

namespace Submission.JacobiTensor

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Injectivity of the Jacobi tensor before `π/2`.**  Along a unit-speed chart geodesic with
sectional curvature `≤ 4` (the project normalisation), the Jacobi tensor `Y` (whose columns are the
Jacobi fields vanishing at `0`) is injective at every time `t₁ < π/2`. -/
theorem jacobiTensor_injective (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    (hunit : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    {t₁ : ℝ} (ht₁pos : 0 < t₁) (ht₁π : t₁ < Real.pi / 2) :
    Function.Injective (Y t₁) := by
  intro a b hab
  set c : E := a - b with hcdef
  set y : ℝ → E := fun s => Y s c with hydef
  have hy0 : y 0 = 0 := by
    simp only [hydef, hY0, ContinuousLinearMap.zero_apply]
  have hyt : y t₁ = 0 := by
    simp only [hydef, hcdef, map_sub, hab, sub_self]
  have hy : ∀ t ∈ Ioo 0 t₁, HasDerivAt y (deriv y t) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 :=
      ⟨by linarith [ht.1], by linarith [ht.2, ht₁π, Real.pi_lt_four]⟩
    have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := c) (hY t ht2)
    simpa only [hydef] using hh.congr_deriv hh.deriv.symm
  have hDy : ∀ t ∈ Ioo 0 t₁, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 :=
      ⟨by linarith [ht.1], by linarith [ht.2, ht₁π, Real.pi_lt_four]⟩
    have hh := hasDerivAt_chartCovDeriv_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (a := c) ht2 hY hU
    simpa only [hydef] using hh.congr_deriv hh.deriv.symm
  have hjac : ∀ t ∈ Ioo 0 t₁, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0 := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 :=
      ⟨by linarith [ht.1], by linarith [ht.2, ht₁π, Real.pi_lt_four]⟩
    simpa only [hydef] using jacobiEquation_col (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (a := c) ht2 hY hU (mem_source_chartCurve (I := I) (h.2.2.1 t ht2))
  have hcont : ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc 0 t₁) := by
    have hycont : ContinuousOn y (Icc 0 t₁) := by
      intro t ht
      have ht2 : t ∈ Ioo (-2 : ℝ) 2 :=
        ⟨by linarith [ht.1], by linarith [ht.2, ht₁π, Real.pi_lt_four]⟩
      exact ((hY t ht2).continuousAt.clm_apply continuousAt_const).continuousWithinAt
    have hucont : ContinuousOn u (Icc 0 t₁) := fun t ht =>
      (h.2.2.2.1 t ⟨by linarith [ht.1], by linarith [ht.2, ht₁π, Real.pi_lt_four]⟩).continuousAt.continuousWithinAt
    have hmem : ∀ t ∈ Icc 0 t₁, u t ∈ (extChartAt I x₀).target := fun t ht =>
      h.2.2.1 t ⟨by linarith [ht.1], by linarith [ht.2, ht₁π, Real.pi_lt_four]⟩
    have hgc := continuousOn_chartGram_curve (I := I) (x₀ := x₀)
      (continuousOn_chartCurve hucont hmem) hycont hycont
      (fun t ht => mem_source_chartCurve (I := I) (hmem t ht))
    exact Real.continuous_sqrt.comp_continuousOn hgc
  have heq := ConjPoint.eqOn_zero_of_jacobi (hcov := ‹ContMDiffCovariantDerivative cov ∞›)
    hmet hpinch htor h hunit ht₁pos ht₁π hy hDy hjac hcont hy0 hyt
  have h0 : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hd0 : (U 0) c - (gammaOp (cov := cov) x₀ u w 0) ((Y 0) c) = c := by
    rw [hY0, hU0]
    simp
  have hh : HasDerivAt y c 0 := by
    have h := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := c) (hY 0 h0)
    exact h.congr_deriv hd0
  have hslope : Filter.Tendsto (fun t => t⁻¹ • (y t - y 0)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa only [zero_add] using hh.tendsto_slope_zero_right
  have hev : (fun t => t⁻¹ • (y t - y 0)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : E)) := by
    filter_upwards [Ioo_mem_nhdsGT ht₁pos] with t ht
    rw [heq t (Ioo_subset_Icc_self ht), hy0, sub_zero, smul_zero]
  have hzero : Filter.Tendsto (fun t => t⁻¹ • (y t - y 0)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) :=
    Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hc0 : c = 0 := tendsto_nhds_unique hslope hzero
  have hab0 : a - b = 0 := by rw [← hcdef]; exact hc0
  exact sub_eq_zero.mp hab0

end

end Submission.JacobiTensor
