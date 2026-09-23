import Submission.IndexIntrinsic

/-!
# The intrinsic index integrand: the pointwise identity, the FTC, and the telescoping

This file continues `Submission/IndexIntrinsic.lean` (which defines the chart-free integrand
`idxAlong` and the chart identity).  It contains the three results that turn `idxAlong` into a tool
for the *global* `σ ≤ κ` (no conjugate point strictly inside a minimising segment; Roadmap §96):

* `hasDerivAt_inner_idxAlong` — **the intrinsic pointwise identity**: along a Jacobi field given in a
  chart, the derivative of `t ↦ ⟪Z t, V t⟫` is the intrinsic index integrand `idxAlong`, where `V` is
  the field and `Z` its covariant derivative.  This is `IndexCorner.indexBilin_eq_neg` (the chart
  derivative) combined with the chart identity `idxAlong_eq_neg_indexIntegrand`;
* `integral_idxAlong_eq_sub` — **the fundamental theorem of calculus**:
  `∫_a^b idxAlong = ⟪Z b,V b⟫ - ⟪Z a,V a⟫`.  The conclusion is *chart independent*: the chart data are
  only used to *describe* `γ`, `V` and `Z` on the interval; the boundary term is intrinsic.  This is
  what makes the chart-wise computations glue;
* `integral_idxAlong_eq_sub_of_pieces` — **the telescoping**: if the boundary formula holds on each
  piece of a partition of `[a,b]`, it holds on `[a,b]` (the intermediate boundary terms cancel).  It
  is the formal "additivity over a chart decomposition" of Roadmap §96.4(i).

All three are stated for an **abstract curve `γ`** and **abstract fields `V`, `Z` along `γ`** (the
fields are related to the chart data by the *eventual* equalities `hV`, `hZ`), so that the same
objects can be restricted to the pieces of a chart cover without type-theoretic bookkeeping.  The
chart data live on a strictly larger interval `Icc A B` with `A < a ≤ b < B`, which is what makes the
"eventually near `t`" hypotheses available at the endpoints of `[a,b]` as well (`Icc_mem_nhds` needs
strict bounds), and is exactly the shape produced by `Submission.ChartPieces.exists_chart_pieces`.

`continuousOn_indexIntegrand_Icc` is the general-interval form of the continuity of the chart index
integrand, used to make the FTC applicable.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.CurvatureVec
open Submission.CurvatureSym
open Submission.Rauch
open Submission.Gauss
open Submission.Curvature
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.IndexForm
open Submission.IndexForm2
open Submission.SecondVar2
open Submission.IndexCorner
open Submission.IndexCorner2
open Submission.ChartIndep
open Submission.IndexIntrinsic

namespace Submission.IndexIntrinsic2

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The intrinsic pointwise identity** (abstract curve and abstract fields): along a Jacobi field
given in a chart, the derivative of `t ↦ ⟪Z t, V t⟫` is the intrinsic index integrand, where `V` is
the field and `Z` its covariant derivative. -/
theorem hasDerivAt_inner_idxAlong (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {u w w' J J' J'' : ℝ → E} {t : ℝ}
    (hsrc : γ t ∈ (chartAt H x₀).source)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hw : HasDerivAt w (w' t) t)
    (hJ : HasDerivAt J (J' t) t)
    (hJ' : HasDerivAt J' (J'' t) t)
    (hjac : DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hV : V =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (J s))
    (hZ : Z =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s)) :
    HasDerivAt (fun s : ℝ => inner ℝ (Z s) (V s)) (idxAlong (cov := cov) γ V Z t) t := by
  have hut : HasDerivAt u (w t) t := hu.self_of_nhds
  have htgt : u t ∈ (extChartAt I x₀).target := hstay.self_of_nhds
  have hsrc' : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) htgt
  have hdQ := hasDerivAt_covDsP_zero (cov := cov) (x₀ := x₀) (u := u) (η := J) (w := w)
    (e := J') (w' := w') (e' := J'') hut hw hJ hJ' htgt hstay
  have hdJ : HasDerivAt J (deriv J t) t := hJ.congr_deriv hJ.deriv.symm
  have hpush := hasDerivAt_chartGram_curve (cov := cov) hmet x₀ hut htgt hstay
    (hdQ.congr_deriv hdQ.deriv.symm) hdJ
  have hQeq : deriv (fun r : ℝ => covDsP cov x₀ u J w J' 0 r) t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t))
          (covDsP cov x₀ u J w J' 0 t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      = DtDsP cov x₀ u J w J' t := by
    simp only [DtDsP, hdQ.deriv, chrB_apply]
  have hReq : deriv J t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (J t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      = DtQ cov x₀ u J w J' t := by
    simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero, chrB_apply]
    rw [christoffelEval_comm (cov := cov) htor x₀ ((extChartAt I x₀).symm (u t)) hsrc' (J t) (w t),
      hJ.deriv]
  have hsum : HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (DtQ cov x₀ u J w J' s) (J s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (J t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u J w J' t)) t :=
    hpush.congr_deriv (by rw [hQeq, hReq]; rfl)
  have hevfun : (fun s : ℝ => chartGram (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) (J s))
      =ᶠ[𝓝 t] (fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (DtQ cov x₀ u J w J' s) (J s)) := by
    filter_upwards [hγeq] with s hs
    rw [hs]
  have hsumγ : HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) (J s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (J t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u J w J' t)) t :=
    hsum.congr_of_eventuallyEq hevfun
  have hidx : idxAlong (cov := cov) γ V Z t = - indexIntegrand cov x₀ u J w J' t :=
    idxAlong_eq_neg_indexIntegrand (cov := cov) htor x₀ hsrc hstay hγeq hu hγmd
      hV.eq_of_nhds hZ.eq_of_nhds
  have hb : indexBilin cov x₀ u w J J' J J' t
      = - (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (J t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u J w J' t)) :=
    indexBilin_eq_neg (cov := cov) hmet htor x₀ hsrc' hjac
  have hb2 : indexBilin cov x₀ u w J J' J J' t = indexIntegrand cov x₀ u J w J' t := rfl
  have hval : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (J t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u J w J' t)
      = idxAlong (cov := cov) γ V Z t := by
    linarith [hb, hb2, hidx]
  have hVZ : (fun s : ℝ => inner ℝ (Z s) (V s))
      =ᶠ[𝓝 t] (fun s : ℝ => chartGram (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) (J s)) := by
    filter_upwards [hV, hZ] with s h1 h2
    rw [h1, h2, chartGram_apply]
  exact (hsumγ.congr_of_eventuallyEq hVZ).congr_deriv hval


/-- Continuity of the index integrand on an arbitrary closed interval. -/
lemma continuousOn_indexIntegrand_Icc (htor : cov.torsion = 0) {x₀ : M} {u η w e : ℝ → E}
    {α β : ℝ} (hu : ContinuousOn u (Icc α β)) (hη : ContinuousOn η (Icc α β))
    (hw : ContinuousOn w (Icc α β)) (he : ContinuousOn e (Icc α β))
    (hmem : ∀ t ∈ Icc α β, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => indexIntegrand cov x₀ u η w e t) (Icc α β) := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc α β) :=
    continuousOn_chartCurve hu hmem
  have hsrc : ∀ t ∈ Icc α β, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hRt := continuousOn_Rt (cov := cov) (x₀ := x₀) htor hu hη hw hmem
  have hGt : ContinuousOn (fun t : ℝ => Gt cov x₀ u η w e t) (Icc α β) := by
    rw [show (fun t : ℝ => Gt cov x₀ u η w e t) = fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (DtQ cov x₀ u η w e t) (DtQ cov x₀ u η w e t) from rfl]
    exact continuousOn_chartGram_curve (I := I) hγ
      (continuousOn_covDsP_along hu hη hw he hmem)
      (continuousOn_covDsP_along hu hη hw he hmem) hsrc
  exact hRt.sub hGt

/-- **Continuity of the intrinsic index integrand** on `[a,b]`, from chart Jacobi data on the
larger interval `Icc A B` (`A < a ≤ b < B`).  The point is that `idxAlong = - indexIntegrand` in the
chart, and the latter is continuous; the "eventually near `t`" hypotheses needed for the chart
identity are available at every `t ∈ Icc a b` because the chart data live on the larger interval. -/
theorem continuousOn_idxAlong (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)}
    {u w w' J J' J'' : ℝ → E} {a b A B : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc A B, HasDerivAt w (w' t) t) (hwc : ContinuousOn w' (Icc A B))
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc A B, HasDerivAt J (J' t) t) (hJc : ContinuousOn J' (Icc A B))
    (hJ' : ∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t) (hJ''c : ContinuousOn J'' (Icc A B))
    (hjac : ∀ t ∈ Icc A B, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hV : ∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t)) :
    ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ V Z t) (Icc a b) := by
  have hsub : ∀ t ∈ Icc a b, t ∈ Icc A B := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : Icc A B ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_lt_of_le hA ht.1) (lt_of_le_of_lt ht.2 hB)
  have hevγ (t : ℝ) (ht : t ∈ Icc a b) : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hγeq s hs)
  have hevu (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hu s hs)
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (hu t (hsub t ht)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt t (hsub t ht)))
  have hsrc (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ (chartAt H x₀).source := by
    rw [hγeq t (hsub t ht)]
    exact mem_source_chartCurve (I := I) (htgt t (hsub t ht))
  have hγmd (t : ℝ) (ht : t ∈ Icc a b) : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (mdifferentiableAt_chartCurve (I := I) (hu t (hsub t ht)) (htgt t (hsub t ht))
      (hstay t ht)).congr_of_eventuallyEq (hevγ t ht)
  have hneg : ContinuousOn (fun t : ℝ => - indexIntegrand cov x₀ u J w J' t) (Icc a b) :=
    (continuousOn_indexIntegrand_Icc (cov := cov) htor
      (HasDerivAt.continuousOn (fun t ht => hu t (hsub t ht)))
      (HasDerivAt.continuousOn (fun t ht => hJ t (hsub t ht)))
      (HasDerivAt.continuousOn (fun t ht => hw t (hsub t ht)))
      (HasDerivAt.continuousOn (fun t ht => hJ' t (hsub t ht)))
      (fun t ht => htgt t (hsub t ht))).neg
  refine hneg.congr ?_
  intro t ht
  exact idxAlong_eq_neg_indexIntegrand (cov := cov) htor x₀ (hsrc t ht) (hstay t ht)
    (hevγ t ht) (hevu t ht) (hγmd t ht) (hV t (hsub t ht)) (hZ t (hsub t ht))

/-- A weakened form of `continuousOn_idxAlong`: the Jacobi equation is not needed, only the
continuity of the four chart functions. -/
theorem continuousOn_idxAlong_weak (htor : cov.torsion = 0) (x₀ : M)
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)}
    {u w J J' : ℝ → E} {a b A B : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (huC : ContinuousOn u (Icc a b)) (hJC : ContinuousOn J (Icc a b))
    (hwC : ContinuousOn w (Icc a b)) (hJ'C : ContinuousOn J' (Icc a b))
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hV : ∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t)) :
    ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ V Z t) (Icc a b) := by
  have hsub : ∀ t ∈ Icc a b, t ∈ Icc A B := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : Icc A B ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_lt_of_le hA ht.1) (lt_of_le_of_lt ht.2 hB)
  have hevγ (t : ℝ) (ht : t ∈ Icc a b) : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hγeq s hs)
  have hevu (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hu s hs)
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (hu t (hsub t ht)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt t (hsub t ht)))
  have hsrc (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ (chartAt H x₀).source := by
    rw [hγeq t (hsub t ht)]
    exact mem_source_chartCurve (I := I) (htgt t (hsub t ht))
  have hγmd (t : ℝ) (ht : t ∈ Icc a b) : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (mdifferentiableAt_chartCurve (I := I) (hu t (hsub t ht)) (htgt t (hsub t ht))
      (hstay t ht)).congr_of_eventuallyEq (hevγ t ht)
  have hneg : ContinuousOn (fun t : ℝ => - indexIntegrand cov x₀ u J w J' t) (Icc a b) :=
    (continuousOn_indexIntegrand_Icc (cov := cov) htor huC hJC hwC hJ'C
      (fun t ht => htgt t (hsub t ht))).neg
  refine hneg.congr ?_
  intro t ht
  exact idxAlong_eq_neg_indexIntegrand (cov := cov) htor x₀ (hsrc t ht) (hstay t ht)
    (hevγ t ht) (hevu t ht) (hγmd t ht) (hV t (hsub t ht)) (hZ t (hsub t ht))

/-- **The fundamental theorem of calculus for the intrinsic index integrand** (abstract curve and
abstract fields).  The chart data describe `γ`, the field `V` and its covariant derivative `Z` on the
interval `Icc A B ⊇ [a,b]` (with room: `A < a ≤ b < B`, which is what makes the "eventually near `t`"
hypotheses of the pointwise identity available at the endpoints of `[a,b]` as well).  The conclusion
is the chart-independent boundary formula. -/
theorem integral_idxAlong_eq_sub (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)}
    {u w w' J J' J'' : ℝ → E} {a b A B : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc A B, HasDerivAt w (w' t) t) (hwc : ContinuousOn w' (Icc A B))
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc A B, HasDerivAt J (J' t) t) (hJc : ContinuousOn J' (Icc A B))
    (hJ' : ∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t) (hJ''c : ContinuousOn J'' (Icc A B))
    (hjac : ∀ t ∈ Icc A B, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hV : ∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t)) :
    ∫ t in a..b, idxAlong (cov := cov) γ V Z t
      = inner ℝ (Z b) (V b) - inner ℝ (Z a) (V a) := by
  have hsub : ∀ t ∈ Icc a b, t ∈ Icc A B := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : Icc A B ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_lt_of_le hA ht.1) (lt_of_le_of_lt ht.2 hB)
  have hevγ (t : ℝ) (ht : t ∈ Icc a b) : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hγeq s hs)
  have hevu (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hu s hs)
  have hevJ (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt J (J' s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hJ s hs)
  have hevJ' (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt J' (J'' s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hJ' s hs)
  have hevV (t : ℝ) (ht : t ∈ Icc a b) :
      V =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (J s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hV s hs)
  have hevZ (t : ℝ) (ht : t ∈ Icc a b) :
      Z =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hZ s hs)
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (hu t (hsub t ht)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt t (hsub t ht)))
  have hsrc (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ (chartAt H x₀).source := by
    rw [hγeq t (hsub t ht)]
    exact mem_source_chartCurve (I := I) (htgt t (hsub t ht))
  have hγmd (t : ℝ) (ht : t ∈ Icc a b) : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (mdifferentiableAt_chartCurve (I := I) (hu t (hsub t ht)) (htgt t (hsub t ht))
      (hstay t ht)).congr_of_eventuallyEq (hevγ t ht)
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun s : ℝ => inner ℝ (Z s) (V s)) (idxAlong (cov := cov) γ V Z t) t := by
    intro t ht
    exact hasDerivAt_inner_idxAlong (cov := cov) hmet htor x₀ (hsrc t ht) (hstay t ht)
      (hevγ t ht) (hevu t ht) (hγmd t ht) (hw t (hsub t ht)) (hJ t (hsub t ht))
      (hJ' t (hsub t ht)) (hjac t (hsub t ht)) (hevV t ht) (hevZ t ht)
  have hint : IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov) γ V Z t) volume a b :=
    (continuousOn_idxAlong (cov := cov) hmet htor x₀ hA hab hB hγeq hu hw hwc htgt hJ hJc hJ' hJ''c
      hjac hV hZ).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [uIcc_of_le hab]) hint

/-- **Telescoping of the intrinsic index integral over a partition.** -/
theorem integral_idxAlong_eq_sub_of_pieces {γ : ℝ → M}
    {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} (hc0 : c 0 = a) (hcN : c N = b)
    (hint : ∀ k < N, IntervalIntegrable
      (fun t : ℝ => idxAlong (cov := cov) γ V Z t) volume (c k) (c (k + 1)))
    (hpiece : ∀ k < N, ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov) γ V Z t
        = inner ℝ (Z (c (k + 1))) (V (c (k + 1))) - inner ℝ (Z (c k)) (V (c k))) :
    ∫ t in a..b, idxAlong (cov := cov) γ V Z t
      = inner ℝ (Z b) (V b) - inner ℝ (Z a) (V a) := by
  rw [← hc0, ← hcN]
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint,
    Finset.sum_congr rfl (fun k hk => hpiece k (Finset.mem_range.mp hk))]
  exact Finset.sum_range_sub (fun k => inner ℝ (Z (c k)) (V (c k))) N

/-! ## Jacobi pieces and the vanishing of the Jacobi integral over a chart cover

`IsJacobiPiece` bundles the chart data of one piece of a cover of a curve: on `[a,b]` (with room
`A < a ≤ b < B`) the curve `γ` is a chart geodesic and the pair `(V,Z)` is the chart representation
of a Jacobi field and its covariant derivative.  The two atomic lemmas
`continuousOn_idxAlong_of_isJacobiPiece` and `integral_idxAlong_eq_sub_of_isJacobiPiece` read the
pointwise identity and the FTC on a piece, and `integral_idxAlong_eq_zero_of_cover` assembles them
over a finite cover: **the integral of the intrinsic index integrand of a Jacobi pair vanishing at
the two ends vanishes** — the chart-independent form of
`IndexCorner.integral_indexIntegrand_of_jacobi`, which is what the global `σ ≤ κ` needs.
-/

/-- **One piece of a chart cover carrying Jacobi data.**  On `[a,b]` (with room `A < a ≤ b < B`),
`γ` is described by a chart geodesic `u` and the pair `(V,Z)` by a chart Jacobi field and its
covariant derivative. -/
def IsJacobiPiece (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (V Z : (t : ℝ) → TangentSpace I (γ t)) (a b A B : ℝ) : Prop :=
  ∃ (x₀ : M) (u w w' J J' J'' : ℝ → E),
    A < a ∧ b < B ∧
    (∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t)) ∧
    (∀ t ∈ Icc A B, HasDerivAt u (w t) t) ∧
    (∀ t ∈ Icc A B, HasDerivAt w (w' t) t) ∧
    ContinuousOn w' (Icc A B) ∧
    (∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target) ∧
    (∀ t ∈ Icc A B, HasDerivAt J (J' t) t) ∧
    ContinuousOn J' (Icc A B) ∧
    (∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t) ∧
    ContinuousOn J'' (Icc A B) ∧
    (∀ t ∈ Icc A B, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0) ∧
    (∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t)) ∧
    (∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t))

/-- The intrinsic index integrand is continuous on `[a,b]` when the piece carries Jacobi data. -/
theorem continuousOn_idxAlong_of_isJacobiPiece (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b A B : ℝ}
    (h : IsJacobiPiece (I := I) cov γ V Z a b A B) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ V Z t) (Icc a b) := by
  obtain ⟨x₀, u, w, w', J, J', J'', hA, hB, hγeq, hu, hw, hwc, htgt, hJ, hJc, hJ', hJ''c, hjac,
    hV, hZ⟩ := h
  exact continuousOn_idxAlong (cov := cov) hmet htor x₀ hA hab hB
    hγeq hu hw hwc htgt hJ hJc hJ' hJ''c hjac hV hZ

/-- The FTC on a Jacobi piece. -/
theorem integral_idxAlong_eq_sub_of_isJacobiPiece (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b A B : ℝ}
    (h : IsJacobiPiece (I := I) cov γ V Z a b A B) (hab : a ≤ b) :
    ∫ t in a..b, idxAlong (cov := cov) γ V Z t
      = inner ℝ (Z b) (V b) - inner ℝ (Z a) (V a) := by
  obtain ⟨x₀, u, w, w', J, J', J'', hA, hB, hγeq, hu, hw, hwc, htgt, hJ, hJc, hJ', hJ''c, hjac,
    hV, hZ⟩ := h
  exact integral_idxAlong_eq_sub (cov := cov) hmet htor x₀ hA hab hB
    hγeq hu hw hwc htgt hJ hJc hJ' hJ''c hjac hV hZ

/-- **The Jacobi integral over a chart cover vanishes.** -/
theorem integral_idxAlong_eq_zero_of_cover (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    {N : ℕ} {c : ℕ → ℝ} {A B : ℕ → ℝ} (hc0 : c 0 = a) (hcN : c N = b)
    (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hpiece : ∀ k < N, IsJacobiPiece (I := I) cov γ V Z (c k) (c (k + 1)) (A k) (B k))
    (hVa : V a = 0) (hVb : V b = 0) :
    ∫ t in a..b, idxAlong (cov := cov) γ V Z t = 0 := by
  have hmain := integral_idxAlong_eq_sub_of_pieces (cov := cov) hc0 hcN
    (fun k hk => (continuousOn_idxAlong_of_isJacobiPiece (cov := cov) hmet htor
      (hpiece k hk) (hmono k hk)).intervalIntegrable_of_Icc (hmono k hk))
    (fun k hk => integral_idxAlong_eq_sub_of_isJacobiPiece (cov := cov) hmet htor
      (hpiece k hk) (hmono k hk))
  rw [hmain, hVb, hVa]; simp

/-! ## The polarised intrinsic index integrand and the corner pairing

`bilAlong` is the polarisation of `idxAlong`: the bilinear form `⟪Z,Y⟫ - ⟪R(V,γ')γ', W⟫` on the pairs
`(V,Z)` and `(W,Y)`, whose diagonal is `idxAlong`.  The polarised pointwise identity
(`hasDerivAt_inner_bilAlong`) is `IndexCorner.indexBilin_eq_neg` read through the chart identity, and
the polarised FTC (`integral_bilAlong_eq_sub`) is the chart-independent boundary formula
`∫_a^b bilAlong = ⟪Z b,W b⟫ - ⟪Z a,W a⟫`.

The payoff is the **corner pairing** `integral_bilAlong_corner`:
`∫_0^{t₀} bilAlong = ⟪∇J(t₀), W(t₀)⟫` for a Jacobi field `J` and a test field `W` with `W 0 = 0`.
For the *broken* Jacobi field (`J` on `[0,t₀]`, `0` on `[t₀,L]`) the second piece contributes
`⟪0,W L⟫ - ⟪0,W t₀⟫ = 0`, so the integral over the whole `[0,L]` is exactly `⟪∇J(t₀), W(t₀)⟫` — the
quantity that contradicts the negative semidefiniteness of the index form of a minimising geodesic
(Roadmap §97.4).
-/

/-- **The polarisation of the intrinsic index integrand**: the bilinear form
`⟪Z,Y⟫ - ⟪R(V,γ')γ', W⟫` on the pair `(V,Z)` and the pair `(W,Y)`, whose diagonal value is
`idxAlong`. -/
noncomputable def bilAlong (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (V W : (t : ℝ) → TangentSpace I (γ t)) (Z Y : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  inner ℝ (Z t) (Y t)
    - inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
        (W t)

/-- `bilAlong` on the diagonal is `idxAlong`. -/
lemma bilAlong_self (γ : ℝ → M) (V : (t : ℝ) → TangentSpace I (γ t))
    (Z : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) :
    bilAlong (cov := cov) γ V V Z Z t = idxAlong (cov := cov) γ V Z t := rfl

/-- **`bilAlong` is the polarisation of `idxAlong`.** -/
lemma bilAlong_polar (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (γ : ℝ → M)
    (V W Z Y : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) :
    2 * bilAlong (cov := cov) γ V W Z Y t
      = idxAlong (cov := cov) γ (fun s => V s + W s) (fun s => Z s + Y s) t
        - idxAlong (cov := cov) γ V Z t - idxAlong (cov := cov) γ W Y t := by
  have hsa : inner ℝ (curvVec cov (γ t) (W t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)) (V t)
      = inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)) (W t) := by
    rw [inner_curvVec_self_adjoint (cov := cov) ‹ContMDiffCovariantDerivative cov ∞› htor hmet,
      real_inner_comm]
  simp only [bilAlong, idxAlong, curvVec_add_left (cov := cov) ‹ContMDiffCovariantDerivative cov ∞›,
    inner_add_left, inner_add_right]
  rw [hsa, real_inner_comm (Z t) (Y t)]
  ring

/-- **Continuity of the polarised intrinsic index integrand**. -/
theorem continuousOn_bilAlong (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)}
    {u w w' J J' J'' Wc Wc' : ℝ → E} {a b A B : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc A B, HasDerivAt w (w' t) t)
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc A B, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t)
    (hV : ∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t))
    (hW : ∀ t ∈ Icc A B, HasDerivAt Wc (Wc' t) t)
    (hWh : ∀ t ∈ Icc A B, W t = frameVector (I := I) x₀ (γ t) (Wc t))
    (hY : ∀ t ∈ Icc A B, Y t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u Wc w Wc' t))
    (hWc'c : ContinuousOn Wc' (Icc A B)) :
    ContinuousOn (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t) (Icc a b) := by
  have hsub : ∀ t ∈ Icc a b, t ∈ Icc A B := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hWc'C : ContinuousOn Wc' (Icc a b) := hWc'c.mono hsub
  have huC : ContinuousOn u (Icc a b) := HasDerivAt.continuousOn (fun t ht => hu t (hsub t ht))
  have hwC : ContinuousOn w (Icc a b) := HasDerivAt.continuousOn (fun t ht => hw t (hsub t ht))
  have hJC : ContinuousOn J (Icc a b) := HasDerivAt.continuousOn (fun t ht => hJ t (hsub t ht))
  have hJ'C : ContinuousOn J' (Icc a b) := HasDerivAt.continuousOn (fun t ht => hJ' t (hsub t ht))
  have hWcC : ContinuousOn Wc (Icc a b) := HasDerivAt.continuousOn (fun t ht => hW t (hsub t ht))

  have hsumV : ∀ t ∈ Icc A B, (fun s => V s + W s) t
      = frameVector (I := I) x₀ (γ t) ((fun s => J s + Wc s) t) := by
    intro t ht
    change V t + W t = frameVector (I := I) x₀ (γ t) (J t + Wc t)
    rw [hV t ht, hWh t ht, frameVector_add]
  have hsumZ : ∀ t ∈ Icc A B, (fun s => Z s + Y s) t
      = frameVector (I := I) x₀ (γ t)
          (DtQ cov x₀ u (fun s => J s + Wc s) w (fun s => J' s + Wc' s) t) := by
    intro t ht
    change Z t + Y t = frameVector (I := I) x₀ (γ t)
      (DtQ cov x₀ u (fun s => J s + Wc s) w (fun s => J' s + Wc' s) t)
    rw [hZ t ht, hY t ht, ← frameVector_add]
    congr 1
    simpa using (DtQ_add_smul (cov := cov) (x₀ := x₀) (u := u) (w := w) (η := J) (e := J')
      (W := Wc) (W' := Wc') (ε := 1) t).symm
  have hc1 : ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ (fun s => V s + W s)
      (fun s => Z s + Y s) t) (Icc a b) :=
    continuousOn_idxAlong_weak (cov := cov) htor x₀ hA hab hB hγeq hu huC
      (hJC.add hWcC) hwC (hJ'C.add hWc'C) htgt hsumV hsumZ
  have hc2 : ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ V Z t) (Icc a b) :=
    continuousOn_idxAlong_weak (cov := cov) htor x₀ hA hab hB hγeq hu huC hJC hwC hJ'C htgt hV hZ
  have hc3 : ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ W Y t) (Icc a b) :=
    continuousOn_idxAlong_weak (cov := cov) htor x₀ hA hab hB hγeq hu huC hWcC hwC hWc'C htgt hWh hY
  have hgoal : ∀ t : ℝ, bilAlong (cov := cov) γ V W Z Y t
      = (idxAlong (cov := cov) γ (fun s => V s + W s) (fun s => Z s + Y s) t
          - idxAlong (cov := cov) γ V Z t - idxAlong (cov := cov) γ W Y t) / 2 := by
    intro t
    have h := bilAlong_polar (cov := cov) hmet htor γ V W Z Y t
    linarith [h]
  refine ContinuousOn.congr ?_ (fun t _ => hgoal t)
  exact (hc1.sub hc2).sub hc3 |>.div_const 2

/-- **The polarised pointwise identity.** -/
theorem hasDerivAt_inner_bilAlong (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)}
    {u w w' J J' J'' Wc Wc' : ℝ → E} {t : ℝ}
    (hsrc : γ t ∈ (chartAt H x₀).source)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hw : HasDerivAt w (w' t) t)
    (hJ : HasDerivAt J (J' t) t)
    (hJ' : HasDerivAt J' (J'' t) t)
    (hjac : DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hV : V =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (J s))
    (hZ : Z =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s))
    (hW : HasDerivAt Wc (Wc' t) t)
    (hWh : W =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (Wc s))
    (hY : Y =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (DtQ cov x₀ u Wc w Wc' s)) :
    HasDerivAt (fun s : ℝ => inner ℝ (Z s) (W s)) (bilAlong (cov := cov) γ V W Z Y t) t := by
  have hut : HasDerivAt u (w t) t := hu.self_of_nhds
  have htgt : u t ∈ (extChartAt I x₀).target := hstay.self_of_nhds
  have hsrc' : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) htgt
  have hpt : γ t = (extChartAt I x₀).symm (u t) := hγeq.self_of_nhds
  have hkey : ∀ (p : M), p ∈ (chartAt H x₀).source → ∀ X Y Z : E,
      chartGram (I := I) x₀ p X (chartCurv cov x₀ p Y Z)
        = chartGram (I := I) x₀ p (chartCurv cov x₀ p X Z) Y := by
    intro p hp X Y Z
    rw [chartGram_comm (I := I) x₀ p X (chartCurv cov x₀ p Y Z),
      chartCurv_self_adjoint (cov := cov) ‹ContMDiffCovariantDerivative cov ∞› htor hmet x₀ hp
        Y Z X,
      chartGram_comm (I := I) x₀ p Y (chartCurv cov x₀ p X Z)]
  have hdQ := hasDerivAt_covDsP_zero (cov := cov) (x₀ := x₀) (u := u) (η := J) (w := w)
    (e := J') (w' := w') (e' := J'') hut hw hJ hJ' htgt hstay
  have hdW : HasDerivAt Wc (deriv Wc t) t := hW.congr_deriv hW.deriv.symm
  have hpush := hasDerivAt_chartGram_curve (cov := cov) hmet x₀ hut htgt hstay
    (hdQ.congr_deriv hdQ.deriv.symm) hdW
  have hQeq : deriv (fun r : ℝ => covDsP cov x₀ u J w J' 0 r) t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t))
          (covDsP cov x₀ u J w J' 0 t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      = DtDsP cov x₀ u J w J' t := by
    simp only [DtDsP, hdQ.deriv, chrB_apply]
  have hReq : deriv Wc t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (Wc t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      = DtQ cov x₀ u Wc w Wc' t := by
    simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero, chrB_apply]
    rw [christoffelEval_comm (cov := cov) htor x₀ ((extChartAt I x₀).symm (u t)) hsrc' (Wc t) (w t),
      hW.deriv]
  have hsum : HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (DtQ cov x₀ u J w J' s) (Wc s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (Wc t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u Wc w Wc' t)) t :=
    hpush.congr_deriv (by rw [hQeq, hReq]; rfl)
  have hevfun : (fun s : ℝ => chartGram (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) (Wc s))
      =ᶠ[𝓝 t] (fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (DtQ cov x₀ u J w J' s) (Wc s)) := by
    filter_upwards [hγeq] with s hs
    rw [hs]
  have hsumγ : HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) (Wc s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (Wc t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u Wc w Wc' t)) t :=
    hsum.congr_of_eventuallyEq hevfun
  -- the value identity
  have hb : indexBilin cov x₀ u w J J' Wc Wc' t
      = - (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (Wc t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u Wc w Wc' t)) :=
    indexBilin_eq_neg (cov := cov) hmet htor x₀ hsrc' hjac
  have hb2 : indexBilin cov x₀ u w J J' Wc Wc' t
      = - bilAlong (cov := cov) γ V W Z Y t := by
    rw [indexBilin_eq, bilAlong, hV.eq_of_nhds, hZ.eq_of_nhds, hWh.eq_of_nhds, hY.eq_of_nhds]
    rw [← frameVector_chartVel_eq_curveVelocity (I := I) hsrc hstay hγeq hu hγmd, hpt]
    rw [Rq_eq_chartGram_chartCurv (cov := cov) htor x₀ hsrc' (w t) (J t) (Wc t),
      curvVec_frameVector_eq (cov := cov) htor x₀ hsrc' (J t) (w t),
      hkey ((extChartAt I x₀).symm (u t)) hsrc' (J t) (Wc t) (w t)]
    simp only [Gq, chartGram_apply]
    ring
  have hval : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (Wc t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u Wc w Wc' t)
      = bilAlong (cov := cov) γ V W Z Y t := by
    linarith [hb, hb2]
  have hVW : (fun s : ℝ => inner ℝ (Z s) (W s))
      =ᶠ[𝓝 t] (fun s : ℝ => chartGram (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) (Wc s)) := by
    filter_upwards [hZ, hWh] with s h1 h2
    rw [h1, h2, chartGram_apply]
  exact (hsumγ.congr_of_eventuallyEq hVW).congr_deriv hval


/-- **The polarised FTC**: the integral of the polarised intrinsic index integrand is the boundary
difference.  The continuity of the integrand is a hypothesis (it follows from the chart identity
`indexBilin = -bilAlong` and the continuity of the chart objects; see the roadmap). -/
theorem integral_bilAlong_eq_sub (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)}
    {u w w' J J' J'' Wc Wc' : ℝ → E} {a b A B : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc A B, HasDerivAt w (w' t) t)
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc A B, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t)
    (hjac : ∀ t ∈ Icc A B, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hV : ∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t))
    (hW : ∀ t ∈ Icc A B, HasDerivAt Wc (Wc' t) t)
    (hWh : ∀ t ∈ Icc A B, W t = frameVector (I := I) x₀ (γ t) (Wc t))
    (hY : ∀ t ∈ Icc A B, Y t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u Wc w Wc' t))
    (hWc'c : ContinuousOn Wc' (Icc A B)) :
    ∫ t in a..b, bilAlong (cov := cov) γ V W Z Y t
      = inner ℝ (Z b) (W b) - inner ℝ (Z a) (W a) := by
  have hsub : ∀ t ∈ Icc a b, t ∈ Icc A B := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : Icc A B ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_lt_of_le hA ht.1) (lt_of_le_of_lt ht.2 hB)
  have hevγ (t : ℝ) (ht : t ∈ Icc a b) : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hγeq s hs)
  have hevu (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hu s hs)
  have hevV (t : ℝ) (ht : t ∈ Icc a b) :
      V =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (J s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hV s hs)
  have hevZ (t : ℝ) (ht : t ∈ Icc a b) :
      Z =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (DtQ cov x₀ u J w J' s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hZ s hs)
  have hevW (t : ℝ) (ht : t ∈ Icc a b) :
      W =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (Wc s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hWh s hs)
  have hevY (t : ℝ) (ht : t ∈ Icc a b) :
      Y =ᶠ[𝓝 t] fun s => frameVector (I := I) x₀ (γ s) (DtQ cov x₀ u Wc w Wc' s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hY s hs)
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (hu t (hsub t ht)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt t (hsub t ht)))
  have hsrc (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ (chartAt H x₀).source := by
    rw [hγeq t (hsub t ht)]
    exact mem_source_chartCurve (I := I) (htgt t (hsub t ht))
  have hγmd (t : ℝ) (ht : t ∈ Icc a b) : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (mdifferentiableAt_chartCurve (I := I) (hu t (hsub t ht)) (htgt t (hsub t ht))
      (hstay t ht)).congr_of_eventuallyEq (hevγ t ht)
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun s : ℝ => inner ℝ (Z s) (W s))
        (bilAlong (cov := cov) γ V W Z Y t) t := by
    intro t ht
    exact hasDerivAt_inner_bilAlong (cov := cov) hmet htor x₀ (hsrc t ht) (hstay t ht)
      (hevγ t ht) (hevu t ht) (hγmd t ht) (hw t (hsub t ht)) (hJ t (hsub t ht))
      (hJ' t (hsub t ht)) (hjac t (hsub t ht)) (hevV t ht) (hevZ t ht) (hW t (hsub t ht))
      (hevW t ht) (hevY t ht)
  have hcont : ContinuousOn (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t) (Icc a b) :=
    continuousOn_bilAlong (cov := cov) hmet htor x₀ hA hab hB hγeq hu hw htgt hJ hJ' hV hZ hW hWh hY
      hWc'c
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [uIcc_of_le hab])
    (hcont.intervalIntegrable_of_Icc hab)

/-- **The corner pairing** (the first piece).  With `W 0 = 0`, the integral of the polarised index
integrand over `[0,t₀]` is the boundary term `⟪Z t₀, W t₀⟫` — the classical "corner" contribution of
a broken Jacobi field.  For the *full* broken field (equal to `(J, ∇J)` on `[0,t₀]` and to `0` on
`[t₀,L]`) the piece `[t₀,L]` contributes `⟪0, W L⟫ - ⟪0, W t₀⟫ = 0`, so the whole integral over
`[0,L]` equals `⟪∇J(t₀), W(t₀)⟫` whenever `W L = 0`. -/
theorem integral_bilAlong_corner (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {γ : ℝ → M} {V Z W Y : (t : ℝ) → TangentSpace I (γ t)}
    {u w w' J J' J'' Wc Wc' : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀)
    {A B : ℝ} (hA : A < 0) (hB : t₀ < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc A B, HasDerivAt w (w' t) t)
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc A B, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc A B, HasDerivAt J' (J'' t) t)
    (hjac : ∀ t ∈ Icc A B, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hV : ∀ t ∈ Icc A B, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc A B, Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u J w J' t))
    (hW : ∀ t ∈ Icc A B, HasDerivAt Wc (Wc' t) t)
    (hWh : ∀ t ∈ Icc A B, W t = frameVector (I := I) x₀ (γ t) (Wc t))
    (hY : ∀ t ∈ Icc A B, Y t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u Wc w Wc' t))
    (hWc'c : ContinuousOn Wc' (Icc A B))
    (hW0 : W 0 = 0) :
    ∫ t in (0 : ℝ)..t₀, bilAlong (cov := cov) γ V W Z Y t
      = inner ℝ (Z t₀) (W t₀) := by
  have hcont : ContinuousOn (fun t : ℝ => bilAlong (cov := cov) γ V W Z Y t) (Icc 0 t₀) :=
    continuousOn_bilAlong (cov := cov) hmet htor x₀ hA (le_of_lt ht₀) hB hγeq hu hw htgt hJ hJ'
      hV hZ hW hWh hY hWc'c
  rw [integral_bilAlong_eq_sub (cov := cov) hmet htor x₀ hA (le_of_lt ht₀) hB hγeq hu hw htgt
    hJ hJ' hjac hV hZ hW hWh hY hWc'c, hW0]
  simp

end

end Submission.IndexIntrinsic2
