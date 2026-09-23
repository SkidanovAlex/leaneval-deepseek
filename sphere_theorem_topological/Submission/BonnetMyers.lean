import Submission.IndexForm2
import Submission.Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div
import Submission.Commons.Analysis.Calculus.intervalIntegral_cos_sq_pi_mul_div
import Submission.ChartCurvCont
import Submission.Pinch
import Submission.Jacobi

/-!
# The index form and Bonnet–Myers

This file continues the second-variation chapter (`Submission/IndexForm.lean`,
`Submission/IndexForm2.lean`).  There we computed the second derivative of the energy of the
straight-line variation of a *chart geodesic*:
`E''(s) = -2 ∫_0^L famK'(s,t) dt`.  Here we evaluate that expression at `s = 0`.

The answer is the classical **index form**: for a chart geodesic `(u,w)` with `w = u'` and a field
`η` along it vanishing at the endpoints (`η 0 = η L = 0`),

`E''(0) = 2 ∫_0^L ( ⟪∇_tη, ∇_tη⟫ - ⟪η, R(η,γ')γ'⟫ ) dt`

where `∇_tη` is the covariant derivative of `η` along the curve (`covDsP … 0`) and
`R(η,γ')γ' = curvVec (ση)(σw)(σw)`.

## Method

1. `famK'(0,t) = ⟪η t, D_sD_tT⟫` (the geodesic equation kills `∇_tT = 0` at `s = 0`), and the
   Ricci identity (`ricci_chart_affine`) splits `D_sD_tT = D_tD_sT + R(η,w)w`.
2. The term `∫ ⟪η, D_tD_sT⟫` is integrated by parts using the metric-compatibility product rule
   (`hasDerivAt_chartGram_curve`): `∫ ⟪η, ∇_t∇_tη⟫ = [⟪η,∇_tη⟫] - ∫ ⟪∇_tη,∇_tη⟫`, and the boundary
   term vanishes because `η 0 = η L = 0`.

## Contents

* `DsDtP`, `DtDsP`: the two second covariant derivatives of the velocity of the variation;
* `ricci_chart_affine'`: the Ricci identity in this notation;
* `hasDerivAt_covDtP_zero`, `hasDerivAt_covDsP_zero`: the pointwise derivatives of `∇_tT` and
  `∇_tη` (`∇_tT` in the variation parameter `s`, `∇_tη` in `t`);
* `famK'_zero`, `famK'_zero_eq`: the value of `famK'` at `s = 0`;
* `index_form`: **the index form identity** at `s = 0`.
## What is proved here (all sorry-free)

* `DsDtP`, `DtDsP`: the two second covariant derivatives of the velocity of the variation;
* `ricci_chart_affine'`: the Ricci identity in this notation (a restatement of
  `SecondVariation.ricci_chart_affine`);
* `hasDerivAt_covDtP_zero`, `hasDerivAt_covDsP_zero`: the pointwise derivatives of `∇_tT` (in the
  variation parameter `s`) and of `∇_tη` (in `t`);
* `famK'_zero`, `famK'_zero_eq`: the value of `famK'` at `s = 0` (uses the geodesic equation to
  kill `∇_tT` and the Ricci identity to split `D_sD_tT`);
* `DtQ`, `Pt`, `Gt`, `Qt`, `Rt`, `indexIntegrand`: the auxiliary functions of the index form
  (`DtQ = ∇_tη`, `Pt = ⟪η,∇_tη⟫`, `Gt = ⟪∇_tη,∇_tη⟫`, `Qt = ⟪η,∇_t∇_tη⟫`, `Rt = ⟪η,R(η,γ')γ'⟫`,
  `indexIntegrand = Rt - Gt`);
* continuity lemmas: `continuousOn_chartCurve`, `continuousOn_chrB_curve`,
  `continuousOn_chartGram_curve`, `continuousOn_dB_curve`, `continuousOn_covDsP_along`,
  `continuousOn_DtDsP`, `continuousOn_indexIntegrand`;
* **`index_identity`**: `∫_0^L famK'(0,t) dt = ∫_0^L indexIntegrand t dt`, i.e. the integration by
  parts that turns the second variation into the index form.  The proof writes
  `famK'(0,·) = (Qt + Gt) + indexIntegrand`, uses the fundamental theorem of calculus for
  `∫(Qt+Gt) = Pt L - Pt 0 = 0` (the boundary terms vanish because `η 0 = η L = 0`) and
  integrability of `famK'(0,·)` and of `Qt + Gt`;
* **`famEnergy_second_deriv_eq`**: the second derivative of the energy of the straight-line
  variation is `-2 ∫ indexIntegrand`, i.e. **the classical index form**
  `E''(0) = -2 ∫_0^L (⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫) dt`.

## The test field (done here as well)

* `testField L Y = sin(π t / L) • Y t`, `testFieldDeriv` its derivative, `hasDerivAt_testField`;
* `covDsP_testField`: **for a parallel field** `Y` (`deriv Y t + Γ(Y t)(w t) = 0`) the covariant
  derivative of the test field is `(π/L) cos(π t/L) • Y t`;
* `indexIntegrand_testField_pointwise`: for a field `Y` which is unit, orthogonal to the velocity
  and parallel, the index integrand of the test field dominates `sin² - (π/L)² cos²`
  (uses `Pinch.one_le_inner_curvVec`);
* `indexIntegrand_testField_integral`: **the estimate** — for `L > 0`,
  `(L² - π²)/(2L) ≤ ∫ indexIntegrand`, hence `> 0` for `L > π`
  (`Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div`,
  `…intervalIntegral_cos_sq_pi_mul_div`, `intervalIntegral.integral_mono_on`).
  So `E''(0) = -2 ∫ indexIntegrand < 0` for `L > π`.

## What remains (the road to Bonnet–Myers `diam M ≤ π`)

1. **Assemble (a)** with the parallel field: `Jacobi.exists_parallel_field_Icc` and
   `Jacobi.chartGram_parallel_const` produce the unit parallel field orthogonal to the velocity
   from a unit vector `Y₀ ⟂ w t₀` (note: `exists_parallel_field_Icc` currently requires
   `Icc a b ⊆ Ioo (-2) 2`, i.e. it is restricted to short geodesics — generalising it to an
   arbitrary chart interval is a prerequisite for using it on long geodesics);
   also provide the integrability hypothesis of `indexIntegrand_testField_integral` (e.g. from
   `famK'(0,·) - (Qt + Gt)` as in `index_identity`).
2. **Minimality.**  If the geodesic segment `γ` from `p` to `q` is minimising
   (`riemannianEDist I p q = ENNReal.ofReal L`) then every fixed-endpoint variation satisfies
   `E(s) ≥ (length)²/L ≥ L = E(0)` (Cauchy–Schwarz, `Manifold.riemannianEDist_le_pathELength`),
   so `E''(0) ≥ 0`.  With `E''(0) < 0` from step 1 this gives `L ≤ π`.
3. **The global version.**  Steps 1+2 as stated are *chart-local*: `index_identity` needs the
   straight-line variation to stay in one chart, and `famEnergy` is a chart quantity.  A geodesic of
   length `> π` does not in general stay in a chart, so the argument must be globalised: cover
   `[0,L]` by finitely many chart intervals, use the **geodesic variation**
   `Ψ(s,t) = exp_{γ(t)}(s η(t))`, and apply the second-variation formula on each piece.  This
   requires the **general-variation second-variation formula** (see below), because the restriction
   of the geodesic variation to a chart is not a straight-line variation, and the pieces cannot be
   glued with straight lines (they disagree at the junctions, and each piece needs `η` to vanish at
   both of its endpoints for the boundary terms of the integration by parts to cancel).

### The general-variation second-variation formula (the next chapter)

Let `Φ : ℝ × ℝ → E` be an arbitrary smooth family in a chart with `U = ∂_sΦ`, `V = ∂_tΦ`, and put
`∇_sX = ∂_sX + Γ(X)(U)`, `∇_tX = ∂_tX + Γ(X)(V)`.  Then, for a family whose `s = 0` curve is a
geodesic (`∇_tV = 0` at `s = 0`) and which fixes the endpoints (`U(s,0) = U(s,L) = 0`),

`E''(0) = 2 ∫_0^L ( ⟪∇_tη, ∇_tη⟫ - ⟪η, R(η,γ')γ'⟫ )`  with `η = U(0,·)`.

The ingredients, all of which have a straight-line analogue already in this file, are:
(a) the product rule in `s` for `⟪X,Y⟫` (`ChartConnection.hasDerivAt_chartGram` applied along the
`s`-curves), giving `E'(s) = 2∫⟪∇_sV,V⟫ = -2∫⟪U,∇_tV⟫`;
(b) **torsion-freeness for a general family**: `∇_sV = ∇_tU` (Clairaut + `chrB_comm`), hence
`∇_sV|_0 = ∇_tη`;
(c) **the Ricci identity for a general family**: `∇_s∇_tX - ∇_t∇_sX = R(U,V)X`, whence
`∇_s∇_sV|_0 = ∇_t∇_tη + R(η,γ')γ'` (the straight-line case is `SecondVariation.ricci_chart_affine`);
(d) integration by parts in `t`: `∫⟪∇_t∇_tη, γ'⟫ = [⟪∇_tη,γ'⟫]_0^L - ∫⟪∇_tη,∇_tγ'⟫ = 0` because the
boundary terms vanish (`U(s,0) = 0` gives `∇_sU|_0(0) = 0`) and `γ'` is parallel.

`index_identity` above is exactly the special case `Φ(s,t) = u t + s • η t`, and
`famK'_zero_eq` is the special case of (c) needed there; the general case must redo the pointwise
chain rules (`hasDerivAt_fam'`, `hasDerivAt_covDtP_s`, … of `Submission/IndexForm.lean`) with
general `Φ`.

## Gotchas learned while writing this file

* `IntervalIntegrable (fun t => <big expression>)` in a statement is expensive/hangs: introduce the
  integrand as a top-level `noncomputable def` (`indexIntegrand`, `DtQ`, `Gt`, …) and/or use
  `IndexForm.intervalIntegrable_slice_of_continuousOn` on a *two-variable* continuous function.
* `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` wants the derivative only on `Ioo a b`;
  use `intervalIntegral.integral_eq_sub_of_hasDerivAt` (with `uIcc`) plus an integrability proof
  instead.
* The interval integral notation swallows trailing `-`: write `(∫ …) - (∫ …)`, and never put an
  explicit `fun t => …` inside `∫ t in a..b, …`.
* `rw [DtDsP]` can fail ("Failed to rewrite using equation theorems"); prefer `simp only [DtDsP]`
  and prove the equality of the two *arguments* separately (`hArg1`, `hArg2`) before rewriting.
* `¬` `HasDerivAt`-derivative values: `hasDerivAt_chartGram_curve` writes the Christoffel term with
  `christoffelEval … (frameVector …)` while `chrB … a b` is the same by definition but not
  syntactically; state helper lemmas in the `christoffelEval … frameVector` form.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.Gauss
open Submission.ChartCurv
open Submission.ChartCurvCont
open Submission.CurvatureVec
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.IndexForm
open Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
open Commons.Geometry.Manifold.Tangent

namespace Submission.BonnetMyers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The two second covariant derivatives of the velocity -/

/-- The second covariant derivative of the velocity `T = ∂_tΨ` of the straight-line variation in
the `t`-direction, differentiated in the *variation parameter* `s`:
`D_sD_tT = ∂_s(∇_tT) + Γ(∇_tT)(∂_sΨ)` at `s = 0`. -/
noncomputable def DsDtP (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e w' e' : ℝ → E) (t : ℝ) : E :=
  deriv (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t) 0
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (covDtP cov x₀ u η w e w' e' 0 t) (η t)

/-- The second covariant derivative of the field `∇_sT = ∇_tη` in the `t`-direction:
`D_tD_sT = ∂_t(∇_sT) + Γ(∇_sT)(γ')` at `s = 0`. -/
noncomputable def DtDsP (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e : ℝ → E) (t : ℝ) : E :=
  deriv (fun r : ℝ => covDsP cov x₀ u η w e 0 r) t
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (covDsP cov x₀ u η w e 0 t) (w t)

/-- **The Ricci identity** in the notation of `DsDtP`/`DtDsP`. -/
theorem ricci_chart_affine' [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u η w e w' e' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀)
    (hη : HasDerivAt η (e t₀) t₀) (he : HasDerivAt e (e' t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 (0 : ℝ), fam u η s t₀ ∈ (extChartAt I x₀).target)
    (hstayt : ∀ᶠ t in 𝓝 t₀, u t ∈ (extChartAt I x₀).target) :
    frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
        (DsDtP cov x₀ u η w e w' e' t₀ - DtDsP cov x₀ u η w e t₀)
      = curvVec cov ((extChartAt I x₀).symm (u t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀)) := by
  simpa only [DsDtP, DtDsP] using
    ricci_chart_affine (cov := cov) htor hu hw hη he htgt hstay hstayt

/-! ## The pointwise derivatives of `∇_t T` and `∇_s T` -/

/-- The derivative in `s` of the velocity `∇_tT` of the straight-line variation, at `s = 0`. -/
theorem hasDerivAt_covDtP_zero [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀)
    (hη : HasDerivAt η (e t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 (0 : ℝ), fam u η s t₀ ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t₀)
      (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀) (w t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (e t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀))) 0 := by
  have hA : HasDerivAt (fun s : ℝ => w' t₀ + s • e' t₀) (e' t₀) 0 := by
    have h1' : HasDerivAt (fun s : ℝ => s • e' t₀) ((1 : ℝ) • e' t₀) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (e' t₀)
    rw [one_smul] at h1'
    have h := (hasDerivAt_const (x := (0 : ℝ)) (c := w' t₀)).add h1'
    rw [zero_add] at h
    exact h
  have hB := hasDerivAt_chrB_fam_s (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w)
    (e := e) (t₀ := t₀) htgt hstay
  have h := hA.add hB
  have hfun : (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t₀)
      = ((fun s : ℝ => w' t₀ + s • e' t₀) + fun s =>
          chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (famP w e s t₀)
            (famP w e s t₀)) := by
    funext s
    rfl
  rw [hfun]
  exact h

/-- The derivative in `t` of `∇_sT = ∇_tη` along the chart curve. -/
theorem hasDerivAt_covDsP_zero [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀)
    (hη : HasDerivAt η (e t₀) t₀) (he : HasDerivAt e (e' t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ t in 𝓝 t₀, u t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun t : ℝ => covDsP cov x₀ u η w e 0 t)
      (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w' t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀))) t₀ := by
  have hC : HasDerivAt (fun t : ℝ => e t + chrB cov x₀ ((extChartAt I x₀).symm (u t))
      (w t) (η t))
      (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w' t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀))) t₀ :=
    he.add (hasDerivAt_chrB_fam_t (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w)
      (e := e) (w' := w') (t₀ := t₀) hu hw hη htgt hstay)
  have hfun : (fun t : ℝ => covDsP cov x₀ u η w e 0 t)
      = (fun t : ℝ => e t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t)) := by
    funext t
    simp only [covDsP, fam, famP, zero_smul, add_zero, zero_add, smul_zero]
  rw [hfun]
  exact hC

/-! ## One-variable continuity helpers -/

/-- A continuous coordinate curve in the chart target gives a continuous chart curve. -/
lemma continuousOn_chartCurve {x₀ : M} {u : ℝ → E} {B : Set ℝ}
    (hu : ContinuousOn u B) (hmem : ∀ t ∈ B, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) B :=
  (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) x₀).continuousOn.comp' hu hmem

/-- Continuity of the chart Christoffel symbol applied to continuous data along a continuous
curve. -/
lemma continuousOn_chrB_curve [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {γ : ℝ → M}
    {X Y : ℝ → E} {B : Set ℝ}
    (hγ : ContinuousOn γ B) (hX : ContinuousOn X B) (hY : ContinuousOn Y B)
    (hmem : ∀ t ∈ B, γ t ∈ (chartAt H x₀).source) :
    ContinuousOn (fun t : ℝ => chrB cov x₀ (γ t) (X t) (Y t)) B :=
  (continuousOn_chrB_prod3 (cov := cov) x₀).comp' (hγ.prodMk (hX.prodMk hY))
    (fun t ht => ⟨hmem t ht, trivial⟩)

/-- Continuity of the chart metric applied to continuous data along a continuous curve. -/
lemma continuousOn_chartGram_curve {x₀ : M} {γ : ℝ → M} {X Y : ℝ → E} {B : Set ℝ}
    (hγ : ContinuousOn γ B) (hX : ContinuousOn X B) (hY : ContinuousOn Y B)
    (hmem : ∀ t ∈ B, γ t ∈ (chartAt H x₀).source) :
    ContinuousOn (fun t : ℝ => chartGram (I := I) x₀ (γ t) (X t) (Y t)) B :=
  (continuousOn_chartGram_prod3 (I := I) x₀).comp' (hγ.prodMk (hX.prodMk hY))
    (fun t ht => ⟨hmem t ht, trivial⟩)

/-- Continuity of `dB` applied to continuous data along a continuous curve. -/
lemma continuousOn_dB_curve [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {γ : ℝ → M}
    {V X Y : ℝ → E} {B : Set ℝ}
    (hγ : ContinuousOn γ B) (hV : ContinuousOn V B) (hX : ContinuousOn X B)
    (hY : ContinuousOn Y B)
    (hmem : ∀ t ∈ B, γ t ∈ (chartAt H x₀).source) :
    ContinuousOn (fun t : ℝ => dB cov x₀ (γ t) (V t) (X t) (Y t)) B := by
  rw [show (fun t : ℝ => dB cov x₀ (γ t) (V t) (X t) (Y t))
      = (fun q' : M × E × E × E => dB cov x₀ q'.1 q'.2.1 q'.2.2.1 q'.2.2.2)
        ∘ fun t : ℝ => (γ t, V t, X t, Y t) from rfl]
  exact (continuousOn_dB_prod (cov := cov) (I := I) x₀).comp'
    (hγ.prodMk (hV.prodMk (hX.prodMk hY))) (fun t ht => ⟨hmem t ht, trivial⟩)

/-- **Continuity of `∇_tη` along the geodesic.** -/
lemma continuousOn_covDsP_along [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e : ℝ → E} {B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B)
    (hw : ContinuousOn w B) (he : ContinuousOn e B)
    (hmem : ∀ t ∈ B, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => covDsP cov x₀ u η w e 0 t) B := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) B :=
    continuousOn_chartCurve hu hmem
  have hsrc : ∀ t ∈ B, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have h1 : ContinuousOn (fun t : ℝ =>
      e t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t)) B :=
    he.add (continuousOn_chrB_curve (cov := cov) hγ hw hη hsrc)
  refine h1.congr ?_
  intro t ht
  simp only [covDsP, fam, famP, zero_smul, add_zero, zero_add, smul_zero]

/-- **Continuity of `D_tD_sT` along the geodesic.** -/
lemma continuousOn_DtDsP [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {L : ℝ}
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hmem : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => DtDsP cov x₀ u η w e t) (Icc 0 L) := by
  have huc : ContinuousOn u (Icc 0 L) := HasDerivAt.continuousOn hu
  have hw0 : ContinuousOn w (Icc 0 L) := HasDerivAt.continuousOn hw
  have hηc : ContinuousOn η (Icc 0 L) := HasDerivAt.continuousOn hη
  have he0 : ContinuousOn e (Icc 0 L) := HasDerivAt.continuousOn he
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc 0 L) :=
    continuousOn_chartCurve huc hmem
  have hsrc : ∀ t ∈ Icc 0 L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hDη : ContinuousOn (fun t : ℝ => covDsP cov x₀ u η w e 0 t) (Icc 0 L) :=
    continuousOn_covDsP_along huc hηc hw0 he0 hmem
  have hderiv_eq : ∀ t ∈ Icc 0 L, deriv (fun r : ℝ => covDsP cov x₀ u η w e 0 r) t
      = e' t + (dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (e t)) := by
    intro t ht
    have hstay : ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hmem t ht))
    exact (hasDerivAt_covDsP_zero (cov := cov) (u := u) (η := η) (w := w) (e := e)
      (w' := w') (e' := e') (hu t ht) (hw t ht) (hη t ht) (he t ht) (hmem t ht) hstay).deriv
  have hmain : ContinuousOn (fun t : ℝ => e' t
      + (dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (e t))
      + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (covDsP cov x₀ u η w e 0 t) (w t))
      (Icc 0 L) :=
    (hec.add (((continuousOn_dB_curve (cov := cov) hγ hw0 hw0 hηc hsrc).add
      (continuousOn_chrB_curve (cov := cov) hγ hwc hηc hsrc)).add
      (continuousOn_chrB_curve (cov := cov) hγ hw0 he0 hsrc))).add
      (continuousOn_chrB_curve (cov := cov) hγ hDη hw0 hsrc)
  refine hmain.congr ?_
  intro t ht
  simp only [DtDsP, hderiv_eq t ht]


/-- The value of `famK'` at `s = 0`: the geodesic equation kills `∇_tT` at `s = 0`, so only the
second factor survives. -/
lemma famK'_zero [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀) (hη : HasDerivAt η (e t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 (0 : ℝ), fam u η s t₀ ∈ (extChartAt I x₀).target)
    (hgeo : w' t₀ + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) = 0) :
    famK' cov x₀ u η w e w' e' 0 t₀
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀)
          (DsDtP cov x₀ u η w e w' e' t₀) := by
  have h0 : covDtP cov x₀ u η w e w' e' 0 t₀ = 0 :=
    covDtP_eq_zero_of_geodesic (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w) (e := e)
      (w' := w') (e' := e') (t := t₀) hgeo
  have hD : deriv (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t₀) 0
      = e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀) (w t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (e t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀)) :=
    (hasDerivAt_covDtP_zero (cov := cov) (u := u) (η := η) (w := w) (e := e) (w' := w')
      (e' := e') hu hw hη htgt hstay).deriv
  have hfc : famCurve (I := I) x₀ u η 0 t₀ = (extChartAt I x₀).symm (u t₀) := by
    simp only [famCurve, fam, zero_smul, add_zero]
  have hP : famP w e 0 t₀ = w t₀ := by simp only [famP, zero_smul, add_zero]
  simp only [famK', hfc, hP, h0, hD, DsDtP, chrB_zero_fst, chartGram_zero_snd, zero_add,
    add_zero]

/-- The value of `famK'` at `s = 0`, split by the Ricci identity into the index integrand. -/
lemma famK'_zero_eq [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u η w e w' e' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀) (hη : HasDerivAt η (e t₀) t₀)
    (he : HasDerivAt e (e' t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 (0 : ℝ), fam u η s t₀ ∈ (extChartAt I x₀).target)
    (hstayt : ∀ᶠ t in 𝓝 t₀, u t ∈ (extChartAt I x₀).target)
    (hgeo : w' t₀ + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) = 0) :
    famK' cov x₀ u η w e w' e' 0 t₀
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀)
          (DtDsP cov x₀ u η w e t₀)
        + inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀))
            (curvVec cov ((extChartAt I x₀).symm (u t₀))
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀))
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀))
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀))) := by
  rw [famK'_zero (cov := cov) hu hw hη htgt hstay hgeo]
  have hric := ricci_chart_affine' (cov := cov) htor hu hw hη he htgt hstay hstayt
  have h1 : frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
        (DsDtP cov x₀ u η w e w' e' t₀)
      - frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (DtDsP cov x₀ u η w e t₀)
      = curvVec cov ((extChartAt I x₀).symm (u t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀)) := by
    rw [← frameVector_sub]
    exact hric
  rw [sub_eq_iff_eq_add] at h1
  rw [chartGram_apply, chartGram_apply, h1, inner_add_right]
  exact add_comm _ _

/-- The covariant derivative of the variation field along the geodesic: `∇_tη`. -/
noncomputable def DtQ (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w e : ℝ → E) : ℝ → E :=
  fun t => covDsP cov x₀ u η w e 0 t

/-- The scalar product `t ↦ ⟪η t, ∇_tη⟫`, whose derivative is the integrand of the index form. -/
noncomputable def Pt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w e : ℝ → E) : ℝ → ℝ :=
  fun t => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t) (DtQ cov x₀ u η w e t)

/-- The first half of the derivative of `Pt`: `⟪∇_tη, ∇_tη⟫`. -/
noncomputable def Gt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w e : ℝ → E) : ℝ → ℝ :=
  fun t => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
    (DtQ cov x₀ u η w e t) (DtQ cov x₀ u η w e t)

/-- The second half of the derivative of `Pt`: `⟪η, ∇_t∇_tη⟫`. -/
noncomputable def Qt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w e : ℝ → E) : ℝ → ℝ :=
  fun t => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t)
    (DtDsP cov x₀ u η w e t)

/-- The curvature term `⟪η, R(η,γ')γ'⟫` of the index form. -/
noncomputable def Rt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w : ℝ → E) : ℝ → ℝ :=
  fun t => inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t))
    (curvVec cov ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))

/-- The integrand of the **index form**: `⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫`, written in the chart
at `x₀` along the curve `t ↦ (extChartAt I x₀).symm (u t)`. -/
noncomputable def indexIntegrand (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u η w e : ℝ → E) (t : ℝ) : ℝ :=
  Rt cov x₀ u η w t - Gt cov x₀ u η w e t

open Submission.IndexForm2 in
/-- **The index form identity, with boundary terms.**  For a chart geodesic `(u,w)` and a field `η`
along it, the integral of `famK'(0,·)` (i.e. minus one half of `E''(0)`) equals the boundary term
`Pt L - Pt 0` plus the integral of the index integrand `⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫`, where
`Pt = ⟪η, ∇_tη⟫`.  (When `η` vanishes at the endpoints, `Pt` does too and one recovers
`index_identity`; the boundary term is what is needed in order to *glue* the identity over a
decomposition of `[0,L]` into chart pieces.) -/
theorem index_identity_boundary [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target) :
    ∫ t in (0:ℝ)..L, famK' cov x₀ u η w e w' e' 0 t
      = (Pt cov x₀ u η w e L - Pt cov x₀ u η w e 0)
        + ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t := by
  have hmem : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target := by
    intro t ht
    have h := hstay 0 ⟨le_of_lt ha₁, le_of_lt ha₂⟩ t
      ⟨by linarith [ht.1], by linarith [ht.2, hL]⟩
    simpa only [fam, zero_smul, add_zero] using h
  have hsub : Icc (0:ℝ) L ⊆ Icc (-1:ℝ) (L+2) := Icc_subset_Icc (by linarith) (by linarith)
  have hsrc : ∀ t ∈ Icc 0 L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc 0 L) :=
    continuousOn_chartCurve (HasDerivAt.continuousOn hu) hmem
  -- the covariant derivative of `η` along the geodesic
  have hDtQval : ∀ t ∈ Icc 0 L, DtQ cov x₀ u η w e t
      = e t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (η t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) := by
    intro t ht
    rw [DtQ]
    simp only [covDsP, fam, famP, zero_smul, add_zero, zero_add, smul_zero, chrB_apply]
    rw [christoffelEval_comm (cov := cov) htor x₀ _ (hsrc t ht) (w t) (η t)]
  have hDtQcont : ContinuousOn (fun t : ℝ => DtQ cov x₀ u η w e t) (Icc 0 L) :=
    continuousOn_covDsP_along (HasDerivAt.continuousOn hu) (HasDerivAt.continuousOn hη)
      (HasDerivAt.continuousOn hw) (HasDerivAt.continuousOn he) hmem
  -- continuity of the two halves of the derivative of `Pt`
  have hGtcont : ContinuousOn (fun t : ℝ => Gt cov x₀ u η w e t) (Icc 0 L) := by
    rw [show (fun t : ℝ => Gt cov x₀ u η w e t) = fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (DtQ cov x₀ u η w e t) (DtQ cov x₀ u η w e t) from rfl]
    exact continuousOn_chartGram_curve (I := I) hγ hDtQcont hDtQcont hsrc
  have hQtcont : ContinuousOn (fun t : ℝ => Qt cov x₀ u η w e t) (Icc 0 L) := by
    rw [show (fun t : ℝ => Qt cov x₀ u η w e t) = fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t) (DtDsP cov x₀ u η w e t) from rfl]
    exact continuousOn_chartGram_curve (I := I) hγ (HasDerivAt.continuousOn hη)
      (continuousOn_DtDsP hu hw hη he hwc hec hmem) hsrc
  have hWcont : ContinuousOn (fun t : ℝ => Qt cov x₀ u η w e t + Gt cov x₀ u η w e t)
      (Icc 0 L) := hQtcont.add hGtcont
  have hWInt : IntervalIntegrable (fun t : ℝ => Qt cov x₀ u η w e t + Gt cov x₀ u η w e t)
      volume 0 L := hWcont.intervalIntegrable_of_Icc hL.le
  -- `Qt + Gt` is the derivative of `Pt`
  have hPtderiv : ∀ t ∈ Icc 0 L, HasDerivAt (Pt cov x₀ u η w e)
      (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t) t := by
    intro t ht
    have hstayt : ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hmem t ht))
    have hD := hasDerivAt_covDsP_zero (cov := cov) (u := u) (η := η) (w := w) (e := e)
      (w' := w') (e' := e') (hu t ht) (hw t ht) (hη t ht) (he t ht) (hmem t ht) hstayt
    have hDform : deriv (fun r : ℝ => covDsP cov x₀ u η w e 0 r) t
        = e' t + (dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (η t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (η t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (e t)) := hD.deriv
    have hpair := hasDerivAt_chartGram_curve (cov := cov) hmet x₀ (hu t ht) (hmem t ht)
      hstayt (hη t ht) hD
    refine hpair.congr_deriv ?_
    have hArg1 : e t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (η t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = DtQ cov x₀ u η w e t := (hDtQval t ht).symm
    have hArg2 : (e' t + (dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (η t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (η t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (e t)))
        + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (covDsP cov x₀ u η w e 0 t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = DtDsP cov x₀ u η w e t := by
      rw [DtDsP, hDform]
      simp only [chrB_apply]
    rw [show Qt cov x₀ u η w e t = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (η t) (DtDsP cov x₀ u η w e t) from rfl,
      show Gt cov x₀ u η w e t = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (DtQ cov x₀ u η w e t) (DtQ cov x₀ u η w e t) from rfl]
    rw [hArg1, hArg2]
    simp only [DtQ]
    ring
  have hPcont : ContinuousOn (Pt cov x₀ u η w e) (Icc 0 L) := by
    rw [show Pt cov x₀ u η w e = fun r : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r)) (η r) (DtQ cov x₀ u η w e r) from rfl]
    exact continuousOn_chartGram_curve (I := I) hγ (HasDerivAt.continuousOn hη) hDtQcont hsrc
  -- the fundamental theorem of calculus
  have hFTC : ∫ t in (0:ℝ)..L, (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t)
      = Pt cov x₀ u η w e L - Pt cov x₀ u η w e 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [Set.uIcc_of_le hL.le] using hPtderiv) hWInt
  -- integrability of `famK'(0,·)`
  have hFamCont : ContinuousOn (fun q : ℝ × ℝ => famK' cov x₀ u η w e w' e' q.1 q.2)
      (Icc a₁ a₂ ×ˢ Icc 0 L) :=
    continuousOn_famK' (cov := cov) (A := Icc a₁ a₂) (B := Icc 0 L)
      (HasDerivAt.continuousOn hu) (HasDerivAt.continuousOn hη) (HasDerivAt.continuousOn hw)
      (HasDerivAt.continuousOn he) hwc hec
      (fun q hq => hstay q.1 hq.1 q.2 (hsub hq.2))
      (fun q hq => mem_source_chartCurve (I := I) (hstay q.1 hq.1 q.2 (hsub hq.2)))
  have hFamInt : IntervalIntegrable (fun t : ℝ => famK' cov x₀ u η w e w' e' 0 t) volume 0 L :=
    intervalIntegrable_slice_of_continuousOn (f := fun q : ℝ × ℝ => famK' cov x₀ u η w e w' e' q.1 q.2)
      (A := Icc a₁ a₂) (L := L) hL.le (by simpa only [Set.uIcc_of_le hL.le] using hFamCont)
      (show (0:ℝ) ∈ Icc a₁ a₂ from ⟨le_of_lt ha₁, le_of_lt ha₂⟩)
  -- the pointwise identity `famK'(0,t) = (Qt + Gt) t + indexIntegrand t`
  have hpoint : ∀ t ∈ Icc 0 L, famK' cov x₀ u η w e w' e' 0 t
      = (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t) + indexIntegrand cov x₀ u η w e t := by
    intro t ht
    have hstay0 : ∀ᶠ s in 𝓝 (0:ℝ), fam u η s t ∈ (extChartAt I x₀).target :=
      Filter.mem_of_superset (Icc_mem_nhds ha₁ ha₂) (fun s hs => hstay s hs t (hsub ht))
    have hstayt : ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hmem t ht))
    rw [famK'_zero_eq (cov := cov) htor (hu t ht) (hw t ht) (hη t ht) (he t ht)
      (hmem t ht) hstay0 hstayt (hgeo t ht)]
    simp only [Qt, Gt, Rt, indexIntegrand]
    ring
  -- assemble
  have hsplit : ∫ t in (0:ℝ)..L, (famK' cov x₀ u η w e w' e' 0 t
        - (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t))
      = (∫ t in (0:ℝ)..L, famK' cov x₀ u η w e w' e' 0 t)
        - (∫ t in (0:ℝ)..L, (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t)) :=
    intervalIntegral.integral_sub hFamInt hWInt
  have hcongr : ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t
      = ∫ t in (0:ℝ)..L, (famK' cov x₀ u η w e w' e' 0 t
        - (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc (0:ℝ) L := by
      rw [Set.uIcc_of_le hL.le] at ht; exact ht
    change indexIntegrand cov x₀ u η w e t = famK' cov x₀ u η w e w' e' 0 t
      - (Qt cov x₀ u η w e t + Gt cov x₀ u η w e t)
    rw [hpoint t htI]
    simp only [indexIntegrand]
    ring
  rw [hcongr, hsplit, hFTC]
  ring

open Submission.IndexForm2 in
/-- **The index form identity.**  For a chart geodesic `(u,w)` and a field `η` along it vanishing
at the endpoints, the integral of `famK'(0,·)` (i.e. minus one half of `E''(0)`) equals the
integral of the index integrand `⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫`. -/
theorem index_identity [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target) :
    ∫ t in (0:ℝ)..L, famK' cov x₀ u η w e w' e' 0 t
      = ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t := by
  rw [index_identity_boundary (cov := cov) hmet htor x₀ hL ha₁ ha₂ hu hw hη he hwc hec hgeo hstay]
  have hLv : Pt cov x₀ u η w e L = 0 := by
    rw [Pt]
    simp only [hηL, chartGram_zero_fst]
  have h0v : Pt cov x₀ u η w e 0 = 0 := by
    rw [Pt]
    simp only [hη0, chartGram_zero_fst]
  rw [hLv, h0v, sub_zero, zero_add]

open Submission.IndexForm2 in
/-- **The second derivative of the energy as the index form.**  For a chart geodesic `(u,w)` and a
field `η` along it vanishing at the endpoints, the second derivative at `s = 0` of the energy of
the straight-line variation is `-2` times the integral of the index integrand
`⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫`. -/
theorem famEnergy_second_deriv_eq [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => famEnergyDeriv cov x₀ u η w e w' e' L s)
      (-2 * ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t) 0 := by
  have hδ₁ : a₁ < a₁ / 2 := by linarith
  have hδ₂ : a₂ / 2 < a₂ := by linarith
  have hδ₀ : a₁ / 2 < 0 := by linarith
  have hδ₀' : 0 < a₂ / 2 := by linarith
  have hE2 := famEnergy_second_deriv (cov := cov) (hmet := hmet) (x₀ := x₀) (L := L) hL.le
    (u := u) (η := η) (w := w) (e := e) (w' := w') (e' := e')
    (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0)
    hδ₁ hδ₂ hδ₀ hδ₀' hu hw hη he hwc hec hstay
  rw [index_identity (cov := cov) hmet htor x₀ hL ha₁ ha₂ hu hw hη he hwc hec hη0 hηL hgeo hstay]
    at hE2
  exact hE2

open Submission.IndexForm2 in
/-- **The second derivative of the energy, with the boundary term.**  For a chart geodesic `(u,w)`
and an arbitrary field `η` along it (no vanishing at the endpoints), the second derivative at
`s = 0` of the energy of the straight-line variation is `-2` times the sum of the boundary term
`Pt L - Pt 0` and the integral of the index integrand. -/
theorem famEnergy_second_deriv_eq_boundary [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => famEnergyDeriv cov x₀ u η w e w' e' L s)
      (-2 * ((Pt cov x₀ u η w e L - Pt cov x₀ u η w e 0)
        + ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t)) 0 := by
  have hδ₁ : a₁ < a₁ / 2 := by linarith
  have hδ₂ : a₂ / 2 < a₂ := by linarith
  have hδ₀ : a₁ / 2 < 0 := by linarith
  have hδ₀' : 0 < a₂ / 2 := by linarith
  have hE2 := famEnergy_second_deriv (cov := cov) (hmet := hmet) (x₀ := x₀) (L := L) hL.le
    (u := u) (η := η) (w := w) (e := e) (w' := w') (e' := e')
    (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0)
    hδ₁ hδ₂ hδ₀ hδ₀' hu hw hη he hwc hec hstay
  rw [index_identity_boundary (cov := cov) hmet htor x₀ hL ha₁ ha₂ hu hw hη he hwc hec hgeo hstay]
    at hE2
  exact hE2

/-- **Continuity of the curvature term `⟪η, R(η,γ')γ'⟫` of the index form.** -/
lemma continuousOn_Rt [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u η w : ℝ → E} {B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (hmem : ∀ t ∈ B, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => Rt cov x₀ u η w t) B := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) B :=
    continuousOn_chartCurve hu hmem
  have hsrc : ∀ t ∈ B, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hdB₁ := continuousOn_dB_curve (cov := cov) (x₀ := x₀) hγ hη hw hw hsrc
  have hdB₂ := continuousOn_dB_curve (cov := cov) (x₀ := x₀) hγ hw hw hη hsrc
  have hchr₁ : ContinuousOn (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t))
      (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)) (η t)) B :=
    continuousOn_chrB_curve (cov := cov) hγ
      (continuousOn_chrB_curve (cov := cov) hγ hw hw hsrc) hη hsrc
  have hchr₂ : ContinuousOn (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t))
      (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t)) (w t)) B :=
    continuousOn_chrB_curve (cov := cov) hγ
      (continuousOn_chrB_curve (cov := cov) hγ hw hη hsrc) hw hsrc
  have harg : ContinuousOn (fun t : ℝ =>
      dB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (w t) (w t)
        - dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t))
            (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)) (η t)
        - chrB cov x₀ ((extChartAt I x₀).symm (u t))
            (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t)) (w t)) B := by
    refine (((hdB₁.sub hdB₂).add hchr₁).sub hchr₂).congr (fun t ht => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
  refine (continuousOn_chartGram_curve (I := I) (x₀ := x₀) hγ hη harg hsrc).congr
    (fun t ht => ?_)
  simp only [Rt]
  rw [curvVec_eq_chart (cov := cov) htor x₀ _ (w t) (w t) (η t) (hsrc t ht)]
  exact (chartGram_apply (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t) _).symm

/-- **Continuity of the integrand of the index form** `⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫`. -/
lemma continuousOn_indexIntegrand' [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u η w e w' e' : ℝ → E} {L : ℝ}
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hmem : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => indexIntegrand cov x₀ u η w e t) (Icc 0 L) := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc 0 L) :=
    continuousOn_chartCurve (HasDerivAt.continuousOn hu) hmem
  have hsrc : ∀ t ∈ Icc 0 L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hRt := continuousOn_Rt (cov := cov) (x₀ := x₀) htor (HasDerivAt.continuousOn hu)
    (HasDerivAt.continuousOn hη) (HasDerivAt.continuousOn hw) hmem
  have hGt : ContinuousOn (fun t : ℝ => Gt cov x₀ u η w e t) (Icc 0 L) := by
    rw [show (fun t : ℝ => Gt cov x₀ u η w e t) = fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (DtQ cov x₀ u η w e t) (DtQ cov x₀ u η w e t) from rfl]
    exact continuousOn_chartGram_curve (I := I) hγ
      (continuousOn_covDsP_along (HasDerivAt.continuousOn hu) (HasDerivAt.continuousOn hη)
        (HasDerivAt.continuousOn hw) (HasDerivAt.continuousOn he) hmem)
      (continuousOn_covDsP_along (HasDerivAt.continuousOn hu) (HasDerivAt.continuousOn hη)
        (HasDerivAt.continuousOn hw) (HasDerivAt.continuousOn he) hmem) hsrc
  exact hRt.sub hGt

/-- **Continuity of the integrand of the index form** (the `t`-derivative of
`t ↦ ⟪η t, ∇_tη⟫`). -/
lemma continuousOn_indexIntegrand [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {L : ℝ}
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hmem : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t) (DtDsP cov x₀ u η w e t)
      + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (covDsP cov x₀ u η w e 0 t) (covDsP cov x₀ u η w e 0 t)) (Icc 0 L) := by
  have huc : ContinuousOn u (Icc 0 L) := HasDerivAt.continuousOn hu
  have hw0 : ContinuousOn w (Icc 0 L) := HasDerivAt.continuousOn hw
  have hηc : ContinuousOn η (Icc 0 L) := HasDerivAt.continuousOn hη
  have he0 : ContinuousOn e (Icc 0 L) := HasDerivAt.continuousOn he
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc 0 L) :=
    continuousOn_chartCurve huc hmem
  have hsrc : ∀ t ∈ Icc 0 L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hDη : ContinuousOn (fun t : ℝ => covDsP cov x₀ u η w e 0 t) (Icc 0 L) :=
    continuousOn_covDsP_along huc hηc hw0 he0 hmem
  exact (continuousOn_chartGram_curve (I := I) hγ hηc
      (continuousOn_DtDsP hu hw hη he hwc hec hmem) hsrc).add
    (continuousOn_chartGram_curve (I := I) hγ hDη hDη hsrc)

/-! ## The test field `sin (π t / L) • E` -/

/-- The test field `sin (π t / L) • E`. -/
def testField (L : ℝ) (Y : ℝ → E) : ℝ → E := (fun t => Real.sin (Real.pi * t / L)) • Y

/-- The derivative of the test field. -/
def testFieldDeriv (L : ℝ) (Y : ℝ → E) : ℝ → E := fun t =>
  (Real.pi / L * Real.cos (Real.pi * t / L)) • Y t
    + Real.sin (Real.pi * t / L) • deriv Y t

lemma hasDerivAt_sin_pi (L t : ℝ) : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t / L))
    (Real.pi / L * Real.cos (Real.pi * t / L)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  have h2 : HasDerivAt (fun t : ℝ => Real.pi * t / L) (Real.pi / L) t := h1.div_const L
  have h3 := (Real.hasDerivAt_sin (Real.pi * t / L)).comp t h2
  refine h3.congr_deriv ?_
  ring

lemma hasDerivAt_testField {L : ℝ} {Y : ℝ → E} {t : ℝ} (hY : HasDerivAt Y (deriv Y t) t) :
    HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t / L) • Y t) (testFieldDeriv (E := E) L Y t) t := by
  have h := (hasDerivAt_sin_pi L t).smul hY
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t / L) • Y t)
      (Real.sin (Real.pi * t / L) • deriv Y t
        + (Real.pi / L * Real.cos (Real.pi * t / L)) • Y t) t := h
  have hcomm : Real.sin (Real.pi * t / L) • deriv Y t
      + (Real.pi / L * Real.cos (Real.pi * t / L)) • Y t
      = testFieldDeriv (E := E) L Y t := by
    rw [testFieldDeriv, add_comm]
  exact h2.congr_deriv hcomm

lemma covDsP_testField {cov : CovariantDerivative I E (TangentSpace I (M := M))} (htor : cov.torsion = 0)
    {x₀ : M} {u w Y : ℝ → E} {L t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hpar : deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0) :
    covDsP cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) 0 t
      = (Real.pi / L * Real.cos (Real.pi * t / L)) • Y t := by
  have hTF : testField (E := E) L Y t = Real.sin (Real.pi * t / L) • Y t := rfl
  have hTFD : testFieldDeriv (E := E) L Y t
      = (Real.pi / L * Real.cos (Real.pi * t / L)) • Y t
        + Real.sin (Real.pi * t / L) • deriv Y t := rfl
  rw [covDsP]
  simp only [fam, famP, zero_smul, add_zero, zero_add, smul_zero]
  rw [hTF, hTFD]
  rw [chrB_smul_snd, chrB_comm (cov := cov) htor hsrc]
  rw [add_assoc, ← smul_add, hpar, smul_zero, add_zero]

lemma indexIntegrand_testField_pointwise (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {x₀ : M} {u w Y : ℝ → E} {L t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1)
    (horth : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0)
    (hwunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hpar : deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0) :
    Real.sin (Real.pi * t / L) ^ 2 - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2
      ≤ indexIntegrand cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) t := by
  have hp : (1 : ℝ) ≤ inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
      (curvVec cov ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) := by
    refine Submission.Pinch.one_le_inner_curvVec hcov hmet hpinch ?_ ?_ ?_
    · simpa only [chartGram_apply] using hunit
    · simpa only [chartGram_apply] using hwunit
    · simpa only [chartGram_apply] using horth
  have hGt : Gt cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) t
      = (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2 := by
    rw [Gt, DtQ, covDsP_testField (cov := cov) htor hsrc hpar]
    simp only [chartGram_smul_smul, hunit, mul_one]
  have hRt : Real.sin (Real.pi * t / L) ^ 2
      ≤ Rt cov x₀ u (testField (E := E) L Y) w t := by
    have hTF' : testField (E := E) L Y t = Real.sin (Real.pi * t / L) • Y t := rfl
    change Real.sin (Real.pi * t / L) ^ 2 ≤
      inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (testField (E := E) L Y t))
        (curvVec cov ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (testField (E := E) L Y t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))
    rw [hTF', frameVector_smul,
      curvVec_smul_left cov hcov]
    rw [real_inner_smul_left, real_inner_smul_right]
    nlinarith [hp, sq_nonneg (Real.sin (Real.pi * t / L))]
  rw [indexIntegrand]
  linarith

/-- The test-field integral bound. -/
theorem indexIntegrand_testField_integral (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) {L : ℝ} (hL : 0 < L) {u w Y : ℝ → E}
    (hsrc : ∀ t ∈ Icc 0 L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hunit : ∀ t ∈ Icc 0 L, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1)
    (horth : ∀ t ∈ Icc 0 L, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0)
    (hwunit : ∀ t ∈ Icc 0 L, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hpar : ∀ t ∈ Icc 0 L, deriv Y t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0)
    (hint : IntervalIntegrable (fun t : ℝ =>
      indexIntegrand cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) t) volume 0 L) :
    (L ^ 2 - Real.pi ^ 2) / (2 * L)
      ≤ ∫ t in (0:ℝ)..L,
          indexIntegrand cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) t := by
  have hpoint : ∀ t ∈ Icc (0:ℝ) L,
      Real.sin (Real.pi * t / L) ^ 2 - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2
        ≤ indexIntegrand cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) t :=
    fun t ht => indexIntegrand_testField_pointwise hcov hmet htor hpinch (hsrc t ht) (hunit t ht)
      (horth t ht) (hwunit t ht) (hpar t ht)
  have hcont2 : ContinuousOn (fun t : ℝ =>
      Real.sin (Real.pi * t / L) ^ 2 - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
      (Icc 0 L) := by fun_prop
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      Real.sin (Real.pi * t / L) ^ 2 - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
      volume 0 L := hcont2.intervalIntegrable_of_Icc hL.le
  have hcont1 : ContinuousOn (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2) (Icc 0 L) := by
    fun_prop
  have hint1 : IntervalIntegrable (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2) volume 0 L :=
    hcont1.intervalIntegrable_of_Icc hL.le
  have hcont3 : ContinuousOn (fun t : ℝ => (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
      (Icc 0 L) := by fun_prop
  have hint3 : IntervalIntegrable (fun t : ℝ =>
      (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2) volume 0 L :=
    hcont3.intervalIntegrable_of_Icc hL.le
  have hsin : ∫ t in (0:ℝ)..L, Real.sin (Real.pi * t / L) ^ 2 = L / 2 :=
    Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div L hL
  have hcos : ∫ t in (0:ℝ)..L, (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2
      = (Real.pi / L) ^ 2 * (L / 2) := by
    have hfun : (fun t : ℝ => (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
        = fun t : ℝ => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2 := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul]
    rw [Commons.Analysis.Calculus.intervalIntegral_cos_sq_pi_mul_div L hL]
  have hval : ∫ t in (0:ℝ)..L, (Real.sin (Real.pi * t / L) ^ 2
      - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2) = (L ^ 2 - Real.pi ^ 2) / (2 * L) := by
    rw [intervalIntegral.integral_sub hint1 hint3, hsin, hcos]
    field_simp
  have hmono := intervalIntegral.integral_mono_on
    (f := fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2
      - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2)
    (g := fun t : ℝ => indexIntegrand cov x₀ u (testField (E := E) L Y) w (testFieldDeriv (E := E) L Y) t)
    (μ := volume) (a := 0) (b := L) hL.le hint2 hint hpoint
  rwa [hval] at hmono


end

end Submission.BonnetMyers
