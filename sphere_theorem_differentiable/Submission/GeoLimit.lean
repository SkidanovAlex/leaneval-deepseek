import Submission.Geodesic
import Submission.GeodesicGlobal
import Submission.Commons.Topology.UniformSpace.tendstoUniformlyOn_comp_of_isCompact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform limit of solutions of the geodesic equation is a solution

This file proves the *closedness* of the geodesic equation under uniform limits, which is the engine
of every compactness argument in the minimisation theory of the length functional (existence of a
shortest geodesic loop, existence of a minimising geodesic between two points in a limit, the
attainment of the cut time).

The statement is local and lives in a fixed chart: if the chart phases `(uₙ, wₙ)`
(position and velocity) of a family of geodesics converge uniformly on `[a,b]`, and the right hand
side `chartGeodesicVectorField` of the chart geodesic equation converges uniformly too, then the
limit phases solve the same equation, hence the limit curve is a geodesic.  The passage to the limit
in the *differential equation* is Mathlib's
`hasDerivAt_of_tendstoLocallyUniformlyOn` (uniform convergence of the derivatives on compact
subintervals of an open set implies differentiability of the limit), together with the convergence
of the curves themselves.

## Contents

* `tendstoUniformlyOn_prod` — the pair of two uniformly convergent families converges uniformly;
* `isGeodesicAt_of_tendstoUniformlyOn` — the main lemma.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GeodesicGlobal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GeoLimit

noncomputable section

/-- The pair of two uniformly convergent families converges uniformly (to the pair of the
limits). -/
theorem tendstoUniformlyOn_prod {α : Type*} [TopologicalSpace α]
    {β : Type*} [PseudoMetricSpace β] {β' : Type*} [PseudoMetricSpace β']
    {ι : Type*} {l : Filter ι} {s : Set α}
    {F : ι → α → β} {f : α → β} {G : ι → α → β'} {g : α → β'}
    (hF : TendstoUniformlyOn F f l s) (hG : TendstoUniformlyOn G g l s) :
    TendstoUniformlyOn (fun n x => (F n x, G n x)) (fun x => (f x, g x)) l s := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  filter_upwards [hF ε hε, hG ε hε] with n hn1 hn2 x hx
  rw [Prod.dist_eq]
  exact max_lt (hn1 x hx) (hn2 x hx)

/-- **A uniform limit of chart solutions of the geodesic equation is a chart solution.**

Let `uₙ, wₙ : ℝ → E` be the chart phases (position and velocity) of a family of geodesics, i.e.
`uₙ' = wₙ` and `wₙ' = chartGeodesicVectorField x₀ (uₙ, wₙ)` on `[a,b]`, with the positions staying
in the chart target.  Assume `uₙ → u` and `wₙ → w` uniformly on `[a,b]`, that the right hand side of
the second equation also converges uniformly
(`chartGeodesicVectorField x₀ (uₙ, wₙ) → chartGeodesicVectorField x₀ (u, w)`), and that the limiting
positions stay in the chart target.  Then `t ↦ (extChartAt I x₀).symm (u t)` is a geodesic at every
`t ∈ (a,b)`. -/
theorem isGeodesicAt_of_tendstoUniformlyOn {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {a b : ℝ} (hab : a < b) {us ws : ℕ → ℝ → E} {u w : ℝ → E}
    (hu : ∀ n, ∀ t ∈ Set.Icc a b, HasDerivAt (us n) (ws n t) t)
    (hw : ∀ n, ∀ t ∈ Set.Icc a b, HasDerivAt (ws n)
      (chartGeodesicVectorField cov x₀ (us n t, ws n t)) t)
    (hustay : ∀ n, ∀ t ∈ Set.Icc a b, us n t ∈ (extChartAt I x₀).target)
    (hut : TendstoUniformlyOn us u Filter.atTop (Set.Icc a b))
    (hwt : TendstoUniformlyOn ws w Filter.atTop (Set.Icc a b))
    (hVF : TendstoUniformlyOn (fun n t => chartGeodesicVectorField cov x₀ (us n t, ws n t))
      (fun t => chartGeodesicVectorField cov x₀ (u t, w t)) Filter.atTop (Set.Icc a b))
    (hstay : ∀ t ∈ Set.Icc a b, u t ∈ (extChartAt I x₀).target) :
    ∀ t ∈ Set.Ioo a b, IsGeodesicAt cov (fun s => (extChartAt I x₀).symm (u s)) t := by
  have hIoo : Set.Ioo a b ⊆ Set.Icc a b := fun _ hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- the limiting position satisfies the first equation
  have hu' : ∀ t ∈ Set.Ioo a b, HasDerivAt u (w t) t := by
    intro t ht
    refine hasDerivAt_of_tendstoLocallyUniformlyOn (f := us) isOpen_Ioo
      (hwt.mono hIoo).tendstoLocallyUniformlyOn ?_ ?_ ht
    · filter_upwards with n x hx
      exact hu n x (hIoo hx)
    · intro x hx
      exact hut.tendsto_at (hIoo hx)
  -- the limiting velocity satisfies the second equation
  have hw' : ∀ t ∈ Set.Ioo a b,
      HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t := by
    intro t ht
    refine hasDerivAt_of_tendstoLocallyUniformlyOn (f := ws) isOpen_Ioo
      (hVF.mono hIoo).tendstoLocallyUniformlyOn ?_ ?_ ht
    · filter_upwards with n x hx
      exact hw n x (hIoo hx)
    · intro x hx
      exact hwt.tendsto_at (hIoo hx)
  intro t ht Z hZ hZeq
  obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Ioo_pos t).mem_iff.mp hZeq
  have htI : t ∈ Set.Ioo (max a (t - δ)) (min b (t + δ)) :=
    ⟨max_lt ht.1 (by linarith), lt_min ht.2 (by linarith)⟩
  refine cov_eq_zero_of_chartGeodesic (v := w) cov x₀ htI ?_ ?_ ?_ Z hZ.contMDiffAt ?_
  · intro s hs
    exact hu' s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  · intro s hs
    exact hw' s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  · intro s hs
    exact hstay s (hIoo ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
  · intro s hs
    exact hδsub ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩

/-- **A uniform limit of geodesics is a geodesic** (the usable form: a compact set of phases
containing all the chart phases of the family). -/
theorem isGeodesicAt_of_tendstoUniformlyOn_of_compactSet
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {a b : ℝ} (hab : a < b)
    {us ws : ℕ → ℝ → E} {u w : ℝ → E}
    (hu : ∀ n, ∀ t ∈ Set.Icc a b, HasDerivAt (us n) (ws n t) t)
    (hw : ∀ n, ∀ t ∈ Set.Icc a b, HasDerivAt (ws n)
      (chartGeodesicVectorField cov x₀ (us n t, ws n t)) t)
    (hustay : ∀ n, ∀ t ∈ Set.Icc a b, us n t ∈ (extChartAt I x₀).target)
    (hut : TendstoUniformlyOn us u Filter.atTop (Set.Icc a b))
    (hwt : TendstoUniformlyOn ws w Filter.atTop (Set.Icc a b))
    (hK : ∃ K : Set (E × E), IsCompact K ∧ K ⊆ (extChartAt I x₀).target ×ˢ (Set.univ : Set E) ∧
      Set.MapsTo (fun t => (u t, w t)) (Set.Icc a b) K ∧
      ∀ n, Set.MapsTo (fun t => (us n t, ws n t)) (Set.Icc a b) K)
    (hstay : ∀ t ∈ Set.Icc a b, u t ∈ (extChartAt I x₀).target) :
    ∀ t ∈ Set.Ioo a b, IsGeodesicAt cov (fun s => (extChartAt I x₀).symm (u s)) t := by
  obtain ⟨K, hKc, hKsub, hKlim, hKn⟩ := hK
  have hVFc : ContinuousOn (fun z : E × E => chartGeodesicVectorField cov x₀ z) K :=
    (ContDiffOn.continuousOn (contDiffOn_chartSpray' (cov := cov) x₀)).mono hKsub
  have hphase : TendstoUniformlyOn (fun n t => (us n t, ws n t)) (fun t => (u t, w t))
      Filter.atTop (Set.Icc a b) := tendstoUniformlyOn_prod hut hwt
  have hVF : TendstoUniformlyOn (fun n t => chartGeodesicVectorField cov x₀ (us n t, ws n t))
      (fun t => chartGeodesicVectorField cov x₀ (u t, w t)) Filter.atTop (Set.Icc a b) := by
    have h := Commons.Topology.UniformSpace.tendstoUniformlyOn_comp_of_isCompact hKc hVFc hphase
      hKlim (Filter.Eventually.of_forall hKn)
    simpa only [Function.comp_def] using h
  exact isGeodesicAt_of_tendstoUniformlyOn hab hu hw hustay hut hwt hVF hstay

end

end Submission.GeoLimit
