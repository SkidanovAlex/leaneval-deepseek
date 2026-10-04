import Submission.SecondVariation
import Submission.Jacobi
import Submission.CurvatureVec
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_uIcc
import Submission.Distance
import Submission.ChartBounds

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second variation of the energy (index form)

This file continues `Submission/SecondVariation.lean` (the Ricci identity for the straight-line
variation of a chart geodesic) and works towards **Bonnet–Myers** (`diam M ≤ π`) and the
**index form**.

## Setting

`u : ℝ → E` is a chart geodesic in the chart at `x₀`, `η : ℝ → E` is a coordinate field along it
(with `η 0 = η L = 0`), and we consider the **straight-line variation**

`Ψ(s,t) = u t + s • η t`   (`fam u η s t`),

with `T = ∂_t Ψ = w + s • e` (`famP w e s t`).  The covariant derivatives along the two parameters
are `covDtP` (`∇_t T`) and `covDsP` (`∇_s T = ∇_t η`) from `Submission.SecondVariation`; they are
related by `∇_s T = ∇_t η` (torsion-freeness, `covDsP_eq_covDtQ`).

The **energy** of the `s`-curve is
`E(s) = famEnergy x₀ u η w e L s = ∫_0^L chartGram x₀ (γ_s t) (T(s,t)) (T(s,t)) dt`,
`γ_s t = (extChartAt I x₀).symm (Ψ(s,t))`.

## What is proved here (all sorry-free)

* `continuousAt_chartGram_prod3`, `continuousOn_chartGram_prod3`, `continuousAt_chrB_prod3`,
  `continuousOn_chrB_prod3`: **joint continuity** of the chart metric and of the chart Christoffel
  symbol as functions of `(p, a, b)` (via basis expansions), on `(chartAt H x₀).source ×ˢ univ`;
* generic composition lemmas `continuousOn_chartGram_comp`, `continuousOn_chrB_comp`,
  `continuousOn_covDsP`, `continuousOn_covDtP`, `continuousOn_famG`, `continuousOn_famG'`,
  `continuousOn_famK`;
* the pointwise derivatives along the variation: `hasDerivAt_fam'`, `hasDerivAt_famP'`,
  `hasDerivAt_fam_t`, `hasDerivAt_famP_t`, `hasDerivAt_chrB_fam_s'` (the general-`s` version of
  `Submission.SecondVariation.hasDerivAt_chrB_fam_s`), `hasDerivAt_covDtP_s` (`∂_s ∇_t T`),
  `hasDerivAt_covDsP_t` (`∂_t ∇_s T`), `hasDerivAt_famG_s` (`∂_s` of the energy integrand),
  `hasDerivAt_chartGram_fam_ST` (the `t`-product rule for `⟪η, T⟫`, needs torsion-freeness),
  `hasDerivAt_famK_s` (`∂_s` of the first-variation integrand `K`);
* **`famEnergy_hasDerivAt`**: the first variation of the energy
  `E'(s₀) = -2 ∫_0^L ⟪η, ∇_t T⟫ dt = -2 ∫ K(s₀,·)`.  It vanishes at `s₀ = 0` for a geodesic.

## Notation/definitions introduced

`famCurve x₀ u η s t`, `famG x₀ u η w e s t`, `famEnergy x₀ u η w e L s`,
`famK cov x₀ u η w e w' e' s t = ⟪η, ∇_t T⟫`,
`famG' cov x₀ u η w e s t = 2⟪∇_s T, T⟫ = ∂_s famG` and
`famK' cov x₀ u η w e w' e' s t = ∂_s famK`.

## Next steps (exactly parallel to `famEnergy_hasDerivAt`)

1. `continuousOn_famK'` (joint continuity of `famK'`); this needs joint continuity of `dB` in
   `(p, v, a, b)` (prove it exactly like `continuousAt_chrB_prod3`, using the basis expansion
   `chrB_eq_sum_gammaEntry` and `mvfderiv_sum_apply`).
2. `famK_hasDerivAt`: `HasDerivAt (fun s => ∫_0^L famK(s,t)dt) (∫_0^L famK'(s₀,t)dt) s₀`,
   with exactly the proof structure of `famEnergy_hasDerivAt` (use `hasDerivAt_famK_s` for the
   pointwise `HasDerivAt` and `continuousOn_famK`/`continuousOn_famK'` for continuity);
   then combine with step 1 and `famEnergy_hasDerivAt` to get `E''(0)`.
3. Evaluate `∫_0^L famK'(0,t)dt`: at `s = 0` the geodesic equation gives `∇_t T(0,·) = 0`
   (`covDtP_eq_zero_of_geodesic`), so the formula `famK'` collapses to
   `⟪η, ∇_s ∇_t T⟫`; use **`ricci_chart_affine`** (`∇_s∇_tT - ∇_t∇_sT = R(η,w)w`), noting
   `∇_s T = ∇_t η` so `∇_t∇_sT(0,·) = ∇_t∇_t η`, and integrate by parts in `t`
   (`hasDerivAt_chartGram_curve` + `intervalIntegral.integral_eq_sub_of_hasDerivAt`; the boundary
   terms vanish because `η 0 = η L = 0`).  The result is the **index form**
   `E''(0) = 2 ∫_0^L ( ⟪∇_tη, ∇_tη⟫ - ⟪η, R(η,w)w⟫ )`.
4. Pinching bound: for `a, b` orthonormal in the chart metric,
   `⟪frameVector a, curvVec (frameVector a) (frameVector b) (frameVector b)⟫ ≥ 1` — combine
   `inner_curvVec_self`, `sectionalCurvature_eq_ratio` and `quarterPinched_sectionalCurvature`
   (see `Submission/Curvature.lean`); `gramFormVec` is computed with `real_inner_self_eq_norm_sq`
   (this DOES work on `TangentSpace I x`, unlike what session 5 feared).
5. `η t = sin (π t / L) • E t` with `E` a unit parallel field orthogonal to `w`
   (`exists_parallel_field_Icc`, `chartGram_parallel_const`); then `∇_tη = (π/L) cos (πt/L) • E`
   and the estimate `E''(0) ≤ π²/L - L < 0` for `L > π` follows from
   `∫_0^L sin²(πt/L) dt = ∫_0^L cos²(πt/L) dt = L/2`.
6. Conclude `E(s) < E(0)` for small `s > 0` (from `E(0) = E'(0) = 0`-ish Taylor data), contradicting
   minimality (`E(s) ≥ (length)²/L ≥ d(γ0,γL)²/L`) — hence `diam M ≤ π` once Hopf–Rinow provides
   minimising geodesics.

## Performance gotchas (hard-won!)

* Writing an `IntervalIntegrable (fun t => <big expression>) volume 0 L` *directly* in a goal makes
  the elaborator hang (deterministic `whnf`/`isDefEq` timeouts even at 32M heartbeats).  The cure is
  to (a) introduce the integrands as `let`-bound functions (`G`, `G'`, `K`) and (b) obtain
  `IntervalIntegrable` from the *generic* helper `intervalIntegrable_slice_of_continuousOn` applied
  to the joint-continuity hypothesis, never from a `ContinuousOn` of the big lambda.
* `simp only [famG', famK]` does not see `let`-bound `G'`/`K`; use `dsimp only [G', K]` first.
* `rw [hvalL] at hFTC` needs `hvalL` stated in the *beta-reduced* form (i.e.
  `chartGram … (η L) … = 0`, not `(fun t => chartGram …) L = 0`).
* `frameVector_zero'` and `ChartBounds`' `chartGram_zero` are the unconditional versions of the
  zero lemmas (the `Submission.Gauss` versions carry `[I.Boundaryless]`).
* `open MeasureTheory` (or `open scoped MeasureTheory`) is needed for the `volume` notation.
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
open Submission.ChartCurv
open Submission.CurvatureVec
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.Distance
open Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
open Commons.Geometry.Manifold.Tangent

namespace Submission.IndexForm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## Joint continuity of the chart metric and the chart Christoffel symbol -/

/-- **Joint continuity of the chart metric** in `(p, a, b)`, at a point of the chart. -/
lemma continuousAt_chartGram_prod3 (x₀ : M) {p₀ : M} (hp₀ : p₀ ∈ (chartAt H x₀).source)
    (a₀ b₀ : E) :
    ContinuousAt (fun q : M × E × E => chartGram (I := I) x₀ q.1 q.2.1 q.2.2) (p₀, a₀, b₀) := by
  have hfun : (fun q : M × E × E => chartGram (I := I) x₀ q.1 q.2.1 q.2.2)
      = fun q : M × E × E => ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr q.2.1 i) * ((Module.finBasis ℝ E).repr q.2.2 j)
              * chartGram (I := I) x₀ q.1 ((Module.finBasis ℝ E) i)
                  ((Module.finBasis ℝ E) j) := by
    funext q
    exact chartGram_eq_sum_repr (I := I) (Module.finBasis ℝ E) x₀ q.1 q.2.1 q.2.2
  rw [hfun]
  refine tendsto_finsetSum Finset.univ fun i _ => ?_
  refine tendsto_finsetSum Finset.univ fun j _ => ?_
  have h1 : ContinuousAt (fun q : M × E × E => (Module.finBasis ℝ E).repr q.2.1 i)
      (p₀, a₀, b₀) :=
    (((continuous_basis_repr (Module.finBasis ℝ E) i).comp
      (continuous_fst.comp continuous_snd))).continuousAt
  have h2 : ContinuousAt (fun q : M × E × E => (Module.finBasis ℝ E).repr q.2.2 j)
      (p₀, a₀, b₀) :=
    (((continuous_basis_repr (Module.finBasis ℝ E) j).comp
      (continuous_snd.comp continuous_snd))).continuousAt
  have h3 : ContinuousAt (fun q : M × E × E =>
      chartGram (I := I) x₀ q.1 ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))
      (p₀, a₀, b₀) :=
    ContinuousAt.comp' (continuousAt_chartGram (I := I) x₀ ((Module.finBasis ℝ E) i)
      ((Module.finBasis ℝ E) j) hp₀) continuousAt_fst
  exact (h1.mul h2).mul h3

/-- **Joint continuity of the chart metric** in `(p, a, b)` on the chart source. -/
lemma continuousOn_chartGram_prod3 (x₀ : M) :
    ContinuousOn (fun q : M × E × E => chartGram (I := I) x₀ q.1 q.2.1 q.2.2)
      ((chartAt H x₀).source ×ˢ (Set.univ : Set (E × E))) :=
  fun _q hq => (continuousAt_chartGram_prod3 (I := I) x₀ hq.1 _ _).continuousWithinAt

/-- **Joint continuity of the chart Christoffel symbol** (`chrB`) in `(p, a, b)`, at a point of the
chart. -/
lemma continuousAt_chrB_prod3 [ContMDiffCovariantDerivative cov ∞] (x₀ : M) {p₀ : M}
    (hp₀ : p₀ ∈ (chartAt H x₀).source) (a₀ b₀ : E) :
    ContinuousAt (fun q : M × E × E => chrB cov x₀ q.1 q.2.1 q.2.2) (p₀, a₀, b₀) := by
  have hev : ∀ᶠ q : M × E × E in 𝓝 (p₀, a₀, b₀), q.1 ∈ (chartAt H x₀).source :=
    continuousAt_fst.tendsto ((chartAt H x₀).open_source.mem_nhds hp₀)
  have hcongr : (fun q : M × E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord i) q.2.1 * ((Module.finBasis ℝ E).coord j) q.2.2)
            • gammaEntry cov x₀ i j q.1)
      =ᶠ[𝓝 (p₀, a₀, b₀)] (fun q : M × E × E => chrB cov x₀ q.1 q.2.1 q.2.2) := by
    filter_upwards [hev] with q hq
    exact (chrB_eq_sum_gammaEntry (cov := cov) x₀ q.1 q.2.1 q.2.2 hq).symm
  refine ContinuousAt.congr ?_ hcongr
  refine tendsto_finsetSum Finset.univ fun i _ => ?_
  refine tendsto_finsetSum Finset.univ fun j _ => ?_
  have hgc : ContinuousAt (fun q : M × E × E => gammaEntry cov x₀ i j q.1) (p₀, a₀, b₀) :=
    ContinuousAt.comp' (((contMDiffOn_gammaEntry (cov := cov) x₀ i j).continuousOn.continuousAt
      ((chartAt H x₀).open_source.mem_nhds hp₀))) continuousAt_fst
  have hci : ContinuousAt (fun q : M × E × E => ((Module.finBasis ℝ E).coord i) q.2.1)
      (p₀, a₀, b₀) :=
    (((LinearMap.continuous_of_finiteDimensional ((Module.finBasis ℝ E).coord i)).comp
      (continuous_fst.comp continuous_snd))).continuousAt
  have hcj : ContinuousAt (fun q : M × E × E => ((Module.finBasis ℝ E).coord j) q.2.2)
      (p₀, a₀, b₀) :=
    (((LinearMap.continuous_of_finiteDimensional ((Module.finBasis ℝ E).coord j)).comp
      (continuous_snd.comp continuous_snd))).continuousAt
  exact (hci.mul hcj).smul hgc

/-- **Joint continuity of the chart Christoffel symbol** on the chart source. -/
lemma continuousOn_chrB_prod3 [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ContinuousOn (fun q : M × E × E => chrB cov x₀ q.1 q.2.1 q.2.2)
      ((chartAt H x₀).source ×ˢ (Set.univ : Set (E × E))) :=
  fun _q hq => (continuousAt_chrB_prod3 (cov := cov) x₀ hq.1 _ _).continuousWithinAt


/-! ## The chart curve and the energy of the straight-line variation -/

/-- The chart curve attached to the straight-line variation `Ψ(s,t) = u t + s • η t`
(`fam`): `γ_s t = (extChartAt I x₀).symm (fam u η s t)`. -/
noncomputable def famCurve (x₀ : M) (u η : ℝ → E) (s t : ℝ) : M :=
  (extChartAt I x₀).symm (fam u η s t)

lemma famCurve_apply (x₀ : M) (u η : ℝ → E) (s t : ℝ) :
    famCurve (I := I) x₀ u η s t = (extChartAt I x₀).symm (fam u η s t) := rfl

/-- The integrand of the energy of the straight-line variation:
`⟪∂_tΨ, ∂_tΨ⟫` in the chart metric. -/
noncomputable def famG (x₀ : M) (u η w e : ℝ → E) (s t : ℝ) : ℝ :=
  chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t) (famP w e s t) (famP w e s t)

/-- The energy of the straight-line variation, `E(s) = ∫_0^L ⟪∂_tΨ, ∂_tΨ⟫ dt`. -/
noncomputable def famEnergy (x₀ : M) (u η w e : ℝ → E) (L s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L, famG (I := I) x₀ u η w e s t

/-! ## Pointwise derivatives along the straight-line variation -/

/-- The derivative of the straight-line variation in `s`, at an arbitrary base point. -/
lemma hasDerivAt_fam' (u η : ℝ → E) (s₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => fam u η s t) (η t) s₀ := by
  show HasDerivAt (fun s : ℝ => u t + s • η t) (η t) s₀
  have h1 : HasDerivAt (fun s : ℝ => s • η t) ((1 : ℝ) • η t) s₀ :=
    (hasDerivAt_id s₀).smul_const (η t)
  rw [one_smul] at h1
  have h := (hasDerivAt_const (x := s₀) (c := u t)).add h1
  rw [zero_add] at h
  exact h

/-- The derivative of the velocity field of the straight-line variation in `s`. -/
lemma hasDerivAt_famP' (w e : ℝ → E) (s₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => famP w e s t) (e t) s₀ := by
  show HasDerivAt (fun s : ℝ => w t + s • e t) (e t) s₀
  have h1 : HasDerivAt (fun s : ℝ => s • e t) ((1 : ℝ) • e t) s₀ :=
    (hasDerivAt_id s₀).smul_const (e t)
  rw [one_smul] at h1
  have h := (hasDerivAt_const (x := s₀) (c := w t)).add h1
  rw [zero_add] at h
  exact h

/-- The derivative of the straight-line variation in `t`. -/
lemma hasDerivAt_fam_t {u η w e : ℝ → E} {s t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hη : HasDerivAt η (e t₀) t₀) :
    HasDerivAt (fun t : ℝ => fam u η s t) (famP w e s t₀) t₀ := by
  have h : HasDerivAt (fun t : ℝ => u t + s • η t) (w t₀ + s • e t₀) t₀ :=
    hu.add (hη.const_smul s)
  exact h

/-- The derivative of the velocity field `famP w e s ·` in `t`. -/
lemma hasDerivAt_famP_t {w e w' e' : ℝ → E} {s t₀ : ℝ} (hw : HasDerivAt w (w' t₀) t₀)
    (he : HasDerivAt e (e' t₀) t₀) :
    HasDerivAt (fun t : ℝ => famP w e s t) (w' t₀ + s • e' t₀) t₀ := by
  exact hw.add (he.const_smul s)

/-- The chain rule in `s` for the Christoffel term of the straight-line variation, at an arbitrary
base point `s₀`. -/
theorem hasDerivAt_chrB_fam_s' [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e : ℝ → E} {s₀ t : ℝ}
    (htgt : fam u η s₀ t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 s₀, fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t))
        (famP w e s t) (famP w e s t))
      (dB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (η t) (famP w e s₀ t) (famP w e s₀ t)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (e t) (famP w e s₀ t)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (famP w e s₀ t) (e t)) s₀ := by
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (v := η t)
    (u := fun s : ℝ => fam u η s t) (a := fun s : ℝ => famP w e s t)
    (b := fun s : ℝ => famP w e s t) (a' := e t) (b' := e t) (t := s₀)
    (hasDerivAt_fam' u η s₀ t) (hasDerivAt_famP' w e s₀ t) (hasDerivAt_famP' w e s₀ t)
    (by simpa using htgt) (by simpa using hstay)
  simpa using h

/-- **The derivative in `s` of `∇_t T`**, where `T = famP w e s ·` is the velocity of the
straight-line variation. -/
theorem hasDerivAt_covDtP_s [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {s₀ t : ℝ}
    (htgt : fam u η s₀ t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 s₀, fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t)
      (e' t + (dB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (η t) (famP w e s₀ t)
            (famP w e s₀ t)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (e t) (famP w e s₀ t)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (famP w e s₀ t) (e t))) s₀ := by
  have hA : HasDerivAt (fun s : ℝ => w' t + s • e' t) (e' t) s₀ := by
    have h1 : HasDerivAt (fun s : ℝ => s • e' t) ((1 : ℝ) • e' t) s₀ :=
      (hasDerivAt_id s₀).smul_const (e' t)
    rw [one_smul] at h1
    have h := (hasDerivAt_const (x := s₀) (c := w' t)).add h1
    rw [zero_add] at h
    exact h
  have hB := hasDerivAt_chrB_fam_s' (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w) (e := e)
    (s₀ := s₀) (t := t) htgt hstay
  have h := hA.add hB
  have hfun : (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t)
      = ((fun s : ℝ => w' t + s • e' t) + fun s : ℝ =>
          chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t)) (famP w e s t)
            (famP w e s t)) := by
    funext s; rfl
  rw [hfun]
  exact h

/-- **The derivative in `t` of `∇_s T = ∇_t η`**, where `T = famP w e s ·`. -/
theorem hasDerivAt_covDsP_t [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' e' : ℝ → E} {s t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀) (hη : HasDerivAt η (e t₀) t₀)
    (he : HasDerivAt e (e' t₀) t₀)
    (htgt : fam u η s t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ t in 𝓝 t₀, fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun t : ℝ => covDsP cov x₀ u η w e s t)
      (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (famP w e s t₀)
            (famP w e s t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (w' t₀ + s • e' t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (famP w e s t₀) (e t₀))) t₀ := by
  have hP : HasDerivAt (fun t : ℝ => famP w e s t) (w' t₀ + s • e' t₀) t₀ :=
    hasDerivAt_famP_t hw he
  have hbase : HasDerivAt (fun t : ℝ => fam u η s t) (famP w e s t₀) t₀ :=
    hasDerivAt_fam_t hu hη
  have hB := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (v := famP w e s t₀)
    (u := fun t : ℝ => fam u η s t) (a := fun t : ℝ => famP w e s t)
    (b := fun t : ℝ => η t) (a' := w' t₀ + s • e' t₀) (b' := e t₀) (t := t₀)
    hbase hP hη (by simpa using htgt) (by simpa using hstay)
  have h := he.add hB
  have hfun : (fun t : ℝ => covDsP cov x₀ u η w e s t)
      = ((fun t : ℝ => e t) + fun t : ℝ =>
          chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t)) (famP w e s t) (η t)) := by
    funext t; rfl
  rw [hfun]
  exact h

/-- **The derivative in `s` of the integrand of the energy** of the straight-line variation. -/
theorem hasDerivAt_famG_s [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M) {u η w e : ℝ → E} {s₀ t : ℝ}
    (htgt : fam u η s₀ t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 s₀, fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s : ℝ => famG (I := I) x₀ u η w e s t)
      (2 * chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s₀ t)
        (covDsP cov x₀ u η w e s₀ t) (famP w e s₀ t)) s₀ := by
  have h := hasDerivAt_chartGram_curve (cov := cov) (hmet := hmet) x₀
    (u := fun s : ℝ => fam u η s t) (v := η t) (t := s₀)
    (hasDerivAt_fam' u η s₀ t) (by simpa using htgt) (by simpa using hstay)
    (h₁ := fun s : ℝ => famP w e s t) (h₂ := fun s : ℝ => famP w e s t)
    (h₁' := e t) (h₂' := e t) (hasDerivAt_famP' w e s₀ t) (hasDerivAt_famP' w e s₀ t)
  refine h.congr_deriv ?_
  simp only [famCurve]
  have hA : (e t + christoffelEval cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t))
        (famP w e s₀ t) (frameVector (I := I) x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (η t)))
      = covDsP cov x₀ u η w e s₀ t := by
    rw [covDsP]
    simp only [chrB]
  rw [hA, two_mul, chartGram_comm (I := I) x₀ _ (famP w e s₀ t)
    (covDsP cov x₀ u η w e s₀ t)]

/-- **The product rule in `t` for `⟪η, T⟫`** along the straight-line variation. -/
theorem hasDerivAt_chartGram_fam_ST [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u η w e w' e' : ℝ → E} {s t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀) (hη : HasDerivAt η (e t₀) t₀)
    (he : HasDerivAt e (e' t₀) t₀)
    (htgt : fam u η s t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ t in 𝓝 t₀, fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun t : ℝ => chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t) (η t)
        (famP w e s t))
      (chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t₀)
          (covDsP cov x₀ u η w e s t₀) (famP w e s t₀)
        + chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t₀) (η t₀)
          (covDtP cov x₀ u η w e w' e' s t₀)) t₀ := by
  have hbase : HasDerivAt (fun t : ℝ => fam u η s t) (famP w e s t₀) t₀ :=
    hasDerivAt_fam_t hu hη
  have hP : HasDerivAt (fun t : ℝ => famP w e s t) (w' t₀ + s • e' t₀) t₀ :=
    hasDerivAt_famP_t hw he
  have h := hasDerivAt_chartGram_curve (cov := cov) (hmet := hmet) x₀
    (u := fun t : ℝ => fam u η s t) (v := famP w e s t₀) (t := t₀)
    hbase (by simpa using htgt) (by simpa using hstay)
    (h₁ := fun t : ℝ => η t) (h₂ := fun t : ℝ => famP w e s t)
    (h₁' := e t₀) (h₂' := w' t₀ + s • e' t₀) hη hP
  refine h.congr_deriv ?_
  simp only [famCurve]
  have hp : (extChartAt I x₀).symm (fam u η s t₀) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (x₀ := x₀) (by simpa using htgt)
  have hA : (e t₀ + christoffelEval cov x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (η t₀)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (famP w e s t₀)))
      = covDsP cov x₀ u η w e s t₀ := by
    rw [covDsP]
    simp only [chrB]
    rw [christoffelEval_comm (cov := cov) htor x₀ _ hp (η t₀) (famP w e s t₀)]
  have hB : (w' t₀ + s • e' t₀ + christoffelEval cov x₀ ((extChartAt I x₀).symm (fam u η s t₀))
        (famP w e s t₀) (frameVector (I := I) x₀ ((extChartAt I x₀).symm (fam u η s t₀))
          (famP w e s t₀))) = covDtP cov x₀ u η w e w' e' s t₀ := by
    rw [covDtP]
    simp only [chrB]
  rw [hA, hB]

/-- **The derivative in `s` of the integrand of the first variation**,
`K(s,t) = ⟪η t, ∇_t T(s,t)⟫`. -/
theorem hasDerivAt_famK_s [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M) {u η w e w' e' : ℝ → E} {s₀ t : ℝ}
    (htgt : fam u η s₀ t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 s₀, fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t) (η t)
        (covDtP cov x₀ u η w e w' e' s t))
      (chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s₀ t)
          (chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (η t) (η t))
          (covDtP cov x₀ u η w e w' e' s₀ t)
        + chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s₀ t) (η t)
          (e' t + (dB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (η t) (famP w e s₀ t)
              (famP w e s₀ t)
            + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (e t) (famP w e s₀ t)
            + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (famP w e s₀ t) (e t))
            + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t))
                (covDtP cov x₀ u η w e w' e' s₀ t) (η t))) s₀ := by
  have hd := hasDerivAt_covDtP_s (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w) (e := e)
    (w' := w') (e' := e') (s₀ := s₀) (t := t) htgt hstay
  have h := hasDerivAt_chartGram_curve (cov := cov) (hmet := hmet) x₀
    (u := fun s : ℝ => fam u η s t) (v := η t) (t := s₀)
    (hasDerivAt_fam' u η s₀ t) (by simpa using htgt) (by simpa using hstay)
    (h₁ := fun s : ℝ => η t) (h₂ := fun s : ℝ => covDtP cov x₀ u η w e w' e' s t)
    (h₁' := (0 : E)) (h₂' := e' t + (dB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (η t)
            (famP w e s₀ t) (famP w e s₀ t)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (e t) (famP w e s₀ t)
        + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s₀ t)) (famP w e s₀ t) (e t)))
    (hasDerivAt_const (x := s₀) (c := η t)) hd
  refine h.congr_deriv ?_
  simp only [famCurve, chrB, zero_add]


/-! ## Joint continuity along the straight-line variation -/

lemma continuousOn_fam_prod {u η : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) :
    ContinuousOn (fun q : ℝ × ℝ => fam u η q.1 q.2) (A ×ˢ B) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => u q.2) (A ×ˢ B) :=
    hu.comp' continuousOn_snd (fun q hq => hq.2)
  have h2 : ContinuousOn (fun q : ℝ × ℝ => η q.2) (A ×ˢ B) :=
    hη.comp' continuousOn_snd (fun q hq => hq.2)
  have h3 : ContinuousOn (fun q : ℝ × ℝ => q.1 • η q.2) (A ×ˢ B) :=
    continuousOn_fst.smul h2
  refine (h1.add h3).congr ?_
  intro q hq
  rfl

lemma continuousOn_famP_prod {w e : ℝ → E} {A B : Set ℝ}
    (hw : ContinuousOn w B) (he : ContinuousOn e B) :
    ContinuousOn (fun q : ℝ × ℝ => famP w e q.1 q.2) (A ×ˢ B) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => w q.2) (A ×ˢ B) :=
    hw.comp' continuousOn_snd (fun q hq => hq.2)
  have h2 : ContinuousOn (fun q : ℝ × ℝ => e q.2) (A ×ˢ B) :=
    he.comp' continuousOn_snd (fun q hq => hq.2)
  have h3 : ContinuousOn (fun q : ℝ × ℝ => q.1 • e q.2) (A ×ˢ B) :=
    continuousOn_fst.smul h2
  refine (h1.add h3).congr ?_
  intro q hq
  rfl

/-- The chart curve of the straight-line variation is continuous on a rectangle on which the
coordinate family stays inside the chart target. -/
lemma continuousOn_famCurve_prod {x₀ : M} {u η : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun q : ℝ × ℝ => famCurve (I := I) x₀ u η q.1 q.2) (A ×ˢ B) :=
  (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) x₀).continuousOn.comp'
    (continuousOn_fam_prod hu hη) hmem

/-- **Joint continuity of the chart metric applied to continuously varying data.** -/
lemma continuousOn_chartGram_comp {x₀ : M} {A B : Set ℝ} {c : ℝ × ℝ → M}
    {X Y : ℝ × ℝ → E}
    (hc : ContinuousOn c (A ×ˢ B)) (hX : ContinuousOn X (A ×ˢ B)) (hY : ContinuousOn Y (A ×ˢ B))
    (hmem : ∀ q ∈ A ×ˢ B, c q ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => chartGram (I := I) x₀ (c q) (X q) (Y q)) (A ×ˢ B) :=
  (continuousOn_chartGram_prod3 (I := I) x₀).comp' (hc.prodMk (hX.prodMk hY))
    (fun q hq => ⟨hmem q hq, trivial⟩)

/-- **Joint continuity of the chart Christoffel symbol applied to continuously varying data.** -/
lemma continuousOn_chrB_comp [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {A B : Set ℝ}
    {c : ℝ × ℝ → M} {X Y : ℝ × ℝ → E}
    (hc : ContinuousOn c (A ×ˢ B)) (hX : ContinuousOn X (A ×ˢ B)) (hY : ContinuousOn Y (A ×ˢ B))
    (hmem : ∀ q ∈ A ×ˢ B, c q ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => chrB cov x₀ (c q) (X q) (Y q)) (A ×ˢ B) :=
  (continuousOn_chrB_prod3 (cov := cov) x₀).comp' (hc.prodMk (hX.prodMk hY))
    (fun q hq => ⟨hmem q hq, trivial⟩)

/-- Continuity of the chart curve data implies continuity of `∇_s T = ∇_t η`. -/
lemma continuousOn_covDsP [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u η w e : ℝ → E}
    {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (he : ContinuousOn e B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => covDsP cov x₀ u η w e q.1 q.2) (A ×ˢ B) := by
  have he' : ContinuousOn (fun q : ℝ × ℝ => e q.2) (A ×ˢ B) :=
    he.comp' continuousOn_snd (fun q hq => hq.2)
  have hP := continuousOn_famP_prod (A := A) (B := B) hw he
  have hη' : ContinuousOn (fun q : ℝ × ℝ => η q.2) (A ×ˢ B) :=
    hη.comp' continuousOn_snd (fun q hq => hq.2)
  have hc := continuousOn_famCurve_prod (x₀ := x₀) hu hη hmem
  have h := he'.add (continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hP hη' hmsrc)
  have hfun : (fun q : ℝ × ℝ => covDsP cov x₀ u η w e q.1 q.2)
      = fun q : ℝ × ℝ => e q.2 + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2)
          (famP w e q.1 q.2) (η q.2) := by
    funext q; rw [covDsP]; rfl
  rw [hfun]; exact h

/-- Continuity of the chart curve data implies continuity of `∇_t T`. -/
lemma continuousOn_covDtP [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u η w e w' e' : ℝ → E}
    {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (he : ContinuousOn e B) (hw' : ContinuousOn w' B) (he' : ContinuousOn e' B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => covDtP cov x₀ u η w e w' e' q.1 q.2) (A ×ˢ B) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => w' q.2 + q.1 • e' q.2) (A ×ˢ B) := by
    refine (hw'.comp' continuousOn_snd (fun q hq => hq.2)).add ?_
    exact continuousOn_fst.smul (he'.comp' continuousOn_snd (fun q hq => hq.2))
  have hP := continuousOn_famP_prod (A := A) (B := B) hw he
  have hc := continuousOn_famCurve_prod (x₀ := x₀) hu hη hmem
  have h := h1.add (continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hP hP hmsrc)
  have hfun : (fun q : ℝ × ℝ => covDtP cov x₀ u η w e w' e' q.1 q.2)
      = fun q : ℝ × ℝ => (w' q.2 + q.1 • e' q.2)
          + chrB cov x₀ (famCurve (I := I) x₀ u η q.1 q.2) (famP w e q.1 q.2)
              (famP w e q.1 q.2) := by
    funext q; rw [covDtP]; rfl
  rw [hfun]; exact h

/-- **The integrand `K = ⟪η, ∇_t T⟫` of the first variation.** -/
noncomputable def famK (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e w' e' : ℝ → E) (s t : ℝ) : ℝ :=
  chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t) (η t)
    (covDtP cov x₀ u η w e w' e' s t)

/-- **The `s`-derivative of the energy integrand (`s ↦ 2⟪∇_s T, T⟫`).** -/
noncomputable def famG' (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e : ℝ → E) (s t : ℝ) : ℝ :=
  2 * chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t)
    (covDsP cov x₀ u η w e s t) (famP w e s t)

/-- **The `s`-derivative of the first-variation integrand.**
(The parenthesisation is chosen to match the derivative produced by `hasDerivAt_famK_s`.) -/
noncomputable def famK' (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e w' e' : ℝ → E) (s t : ℝ) : ℝ :=
  (chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t)
      (chrB cov x₀ (famCurve (I := I) x₀ u η s t) (η t) (η t))
      (covDtP cov x₀ u η w e w' e' s t)
    + chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s t) (η t)
      (e' t + (dB cov x₀ (famCurve (I := I) x₀ u η s t) (η t) (famP w e s t)
          (famP w e s t)
        + chrB cov x₀ (famCurve (I := I) x₀ u η s t) (e t) (famP w e s t)
        + chrB cov x₀ (famCurve (I := I) x₀ u η s t) (famP w e s t) (e t))
        + chrB cov x₀ (famCurve (I := I) x₀ u η s t)
            (covDtP cov x₀ u η w e w' e' s t) (η t)))

/-- **Joint continuity of the energy integrand** on a rectangle where the family stays in the
chart. -/
lemma continuousOn_famG {x₀ : M} {u η w e : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (he : ContinuousOn e B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => famG (I := I) x₀ u η w e q.1 q.2) (A ×ˢ B) := by
  have hc := continuousOn_famCurve_prod (x₀ := x₀) hu hη hmem
  have hP := continuousOn_famP_prod (A := A) (B := B) hw he
  exact continuousOn_chartGram_comp (x₀ := x₀) hc hP hP hmsrc

/-- **Joint continuity of the `s`-derivative of the energy integrand.** -/
lemma continuousOn_famG' [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u η w e : ℝ → E}
    {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (he : ContinuousOn e B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => famG' cov x₀ u η w e q.1 q.2) (A ×ˢ B) := by
  have hc := continuousOn_famCurve_prod (x₀ := x₀) hu hη hmem
  have hP := continuousOn_famP_prod (A := A) (B := B) hw he
  have hD := continuousOn_covDsP (cov := cov) (x₀ := x₀) hu hη hw he hmem hmsrc
  exact continuousOn_const.mul (continuousOn_chartGram_comp (x₀ := x₀) hc hD hP hmsrc)

/-- **Joint continuity of the first-variation integrand `K`.** -/
lemma continuousOn_famK [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u η w e w' e' : ℝ → E}
    {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hw : ContinuousOn w B)
    (he : ContinuousOn e B) (hw' : ContinuousOn w' B) (he' : ContinuousOn e' B)
    (hmem : ∀ q ∈ A ×ˢ B, fam u η q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => famK cov x₀ u η w e w' e' q.1 q.2) (A ×ˢ B) := by
  have hc := continuousOn_famCurve_prod (x₀ := x₀) hu hη hmem
  have hη' : ContinuousOn (fun q : ℝ × ℝ => η q.2) (A ×ˢ B) :=
    hη.comp' continuousOn_snd (fun q hq => hq.2)
  have hD := continuousOn_covDtP (cov := cov) (x₀ := x₀) hu hη hw he hw' he' hmem hmsrc
  exact continuousOn_chartGram_comp (x₀ := x₀) hc hη' hD hmsrc


/-! ## The first variation of the energy -/

/-- An interval integral of a slice of a continuous function on a product of intervals. -/
lemma intervalIntegrable_slice_of_continuousOn {f : ℝ × ℝ → ℝ} {A : Set ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ContinuousOn f (A ×ˢ uIcc (0 : ℝ) L)) {s₀ : ℝ} (hs : s₀ ∈ A) :
    IntervalIntegrable (fun t : ℝ => f (s₀, t)) MeasureTheory.volume 0 L :=
  (hf.comp' (ContinuousOn.prodMk continuousOn_const
    (continuousOn_id : ContinuousOn (fun t : ℝ => t) (uIcc (0 : ℝ) L)))
    (fun t ht => ⟨hs, ht⟩)).intervalIntegrable

/-- **The first variation of the energy of the straight-line variation.**
For the straight-line variation `Ψ(s,t) = u t + s • η t` with `η 0 = η L = 0`, the energy
`E(s) = ∫_0^L ⟪∂_tΨ, ∂_tΨ⟫ dt` has derivative `-2 ∫_0^L ⟪η, ∇_t T⟫ dt` at `s₀`; this is the
first variation formula (it vanishes at `s₀ = 0` for a geodesic). -/
theorem famEnergy_hasDerivAt [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 ≤ L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ δ₁ δ₂ s₀ : ℝ} (ha₁ : a₁ < δ₁) (ha₂ : δ₂ < a₂)
    (h₁ : δ₁ < s₀) (h₂ : s₀ < δ₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2),
      fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => famEnergy (I := I) x₀ u η w e L s)
      (-2 * ∫ t in (0 : ℝ)..L, famK cov x₀ u η w e w' e' s₀ t) s₀ := by
  have huC : ContinuousOn u (Icc 0 L) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc 0 L) := HasDerivAt.continuousOn hw
  have hηC : ContinuousOn η (Icc 0 L) := HasDerivAt.continuousOn hη
  have heC : ContinuousOn e (Icc 0 L) := HasDerivAt.continuousOn he
  have ht_sub : Icc (0 : ℝ) L ⊆ Icc (-1 : ℝ) (L+2) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsubs : Icc δ₁ δ₂ ⊆ Icc a₁ a₂ := Icc_subset_Icc ha₁.le ha₂.le
  have hs_mem : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc 0 L,
      fam u η q.1 q.2 ∈ (extChartAt I x₀).target :=
    fun q hq => hstay q.1 (hsubs hq.1) q.2 (ht_sub hq.2)
  have hs_nhds : ∀ {s : ℝ}, a₁ < s → s < a₂ →
      ∀ t ∈ Icc 0 L, ∀ᶠ s' in 𝓝 s, fam u η s' t ∈ (extChartAt I x₀).target :=
    fun hs₁ hs₂ t ht => Filter.mem_of_superset (Icc_mem_nhds hs₁ hs₂)
      (fun s' hs' => hstay s' hs' t (ht_sub ht))
  have hs₀I : s₀ ∈ Icc δ₁ δ₂ := ⟨le_of_lt h₁, le_of_lt h₂⟩
  have hs₀I' : s₀ ∈ Icc a₁ a₂ := hsubs hs₀I
  -- the concrete integrands
  let G : ℝ → ℝ → ℝ := fun s t => famG (I := I) x₀ u η w e s t
  let G' : ℝ → ℝ → ℝ := fun s t => famG' cov x₀ u η w e s t
  let K : ℝ → ℝ := fun t => famK cov x₀ u η w e w' e' s₀ t
  have hsrc : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc 0 L,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source :=
    fun q hq => mem_source_chartCurve (I := I) (x₀ := x₀) (hs_mem q hq)
  have hGcont_ : ContinuousOn (fun q : ℝ × ℝ => famG (I := I) x₀ u η w e q.1 q.2)
      (Icc δ₁ δ₂ ×ˢ Icc 0 L) :=
    continuousOn_famG (x₀ := x₀) huC hηC hwC heC hs_mem hsrc
  have hG'cont_ : ContinuousOn (fun q : ℝ × ℝ => famG' cov x₀ u η w e q.1 q.2)
      (Icc δ₁ δ₂ ×ˢ Icc 0 L) :=
    continuousOn_famG' (cov := cov) (x₀ := x₀) huC hηC hwC heC hs_mem hsrc
  have hGcont : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) (Icc δ₁ δ₂ ×ˢ uIcc 0 L) := by
    rw [Set.uIcc_of_le hL]; exact hGcont_
  have hG'cont : ContinuousOn (fun q : ℝ × ℝ => G' q.1 q.2) (Icc δ₁ δ₂ ×ˢ uIcc 0 L) := by
    rw [Set.uIcc_of_le hL]; exact hG'cont_
  have hderiv : ∀ s ∈ Icc δ₁ δ₂, ∀ t ∈ uIcc 0 L,
      HasDerivAt (fun s' : ℝ => G s' t) (G' s t) s := by
    intro s hs t ht
    have htI : t ∈ Icc 0 L := by rw [Set.uIcc_of_le hL] at ht; exact ht
    have hs₁ : a₁ < s := lt_of_lt_of_le ha₁ hs.1
    have hs₂ : s < a₂ := lt_of_le_of_lt hs.2 ha₂
    exact hasDerivAt_famG_s (cov := cov) hmet x₀
      (hstay s ⟨hs₁.le, hs₂.le⟩ t (ht_sub htI)) (hs_nhds hs₁ hs₂ t htI)
  have hmain : HasDerivAt (fun s => famEnergy (I := I) x₀ u η w e L s) (∫ t in (0:ℝ)..L, G' s₀ t) s₀ :=
    Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_uIcc
      (F := G) (F' := G') h₁ h₂ hGcont hG'cont hderiv
  -- the integral of `G'` is `-2 ∫ K`
  have hFt : ∀ t ∈ uIcc (0 : ℝ) L, HasDerivAt
      (fun t' : ℝ => chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s₀ t') (η t')
        (famP w e s₀ t')) (G' s₀ t / 2 + K t) t := by
    intro t ht
    have htI : t ∈ Icc 0 L := by rw [Set.uIcc_of_le hL] at ht; exact ht
    have h := hasDerivAt_chartGram_fam_ST (cov := cov) (hmet := hmet) (htor := htor) x₀
      (u := u) (η := η) (w := w) (e := e) (w' := w') (e' := e')
      (s := s₀) (t₀ := t) (hu t htI) (hw t htI) (hη t htI) (he t htI)
      (hstay s₀ hs₀I' t (ht_sub htI))
      (Filter.mem_of_superset (Icc_mem_nhds (show (-1:ℝ) < t by linarith [htI.1])
        (show t < L + 2 by linarith [htI.2])) (fun t' ht' => hstay s₀ hs₀I' t' ht'))
    refine h.congr_deriv ?_
    dsimp only [G', K]
    simp only [famG', famK]
    ring
  have hKcont : ContinuousOn (fun q : ℝ × ℝ => famK cov x₀ u η w e w' e' q.1 q.2)
      (Icc δ₁ δ₂ ×ˢ uIcc 0 L) := by
    rw [Set.uIcc_of_le hL]
    exact continuousOn_famK (cov := cov) (x₀ := x₀) huC hηC hwC heC hwc hec hs_mem hsrc
  have hint1 : IntervalIntegrable (fun t : ℝ => G' s₀ t / 2) volume 0 L :=
    (intervalIntegrable_slice_of_continuousOn hL hG'cont hs₀I).div_const 2
  have hint2 : IntervalIntegrable K volume 0 L :=
    intervalIntegrable_slice_of_continuousOn hL hKcont hs₀I
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hFt (hint1.add hint2)
  have hvalL : chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s₀ L) (η L)
      (famP w e s₀ L) = 0 := by
    rw [hηL, chartGram_apply, frameVector_zero', inner_zero_left]
  have hval0 : chartGram (I := I) x₀ (famCurve (I := I) x₀ u η s₀ 0) (η 0)
      (famP w e s₀ 0) = 0 := by
    rw [hη0, chartGram_apply, frameVector_zero', inner_zero_left]
  rw [hvalL, hval0, sub_zero] at hFTC
  rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_div] at hFTC
  have hKeq : (∫ t in (0 : ℝ)..L, K t) = ∫ t in (0 : ℝ)..L, famK cov x₀ u η w e w' e' s₀ t := rfl
  have hGeq : (∫ t in (0 : ℝ)..L, G' s₀ t) = ∫ t in (0 : ℝ)..L, famG' cov x₀ u η w e s₀ t := rfl
  have hGint : (∫ t in (0 : ℝ)..L, famG' cov x₀ u η w e s₀ t)
      = -2 * ∫ t in (0 : ℝ)..L, famK cov x₀ u η w e w' e' s₀ t := by
    rw [← hGeq, ← hKeq]
    linarith
  rwa [hGint] at hmain

end

end Submission.IndexForm
