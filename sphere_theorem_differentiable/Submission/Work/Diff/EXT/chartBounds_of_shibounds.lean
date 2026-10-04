import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.chartData_step
import Submission.Work.Diff.EXT.chartBounds_of_componentwise
import Submission.Work.Diff.EXT.gram_data_bounds_v2
import Submission.Work.Diff.EXT.gram_det_bound
import Submission.Work.Diff.EXT.chartData_contDiffOn
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.chartMat_fderiv_basis
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_from_reactionPar
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- NB.  Import hygiene: this module imports `local_ext_of_bounded_curv` (hence `EXT/ricCore`) and
-- `GE/norms_defs`, so nothing in its import closure may declare a second `Work.Diff.EXT.SmoothField`
-- or a second `Work.Diff.GE.rot5`.  The `ConnDefs` abbreviation has been renamed to `SmoothFieldC`
-- for that reason, and `covKAExt_frame_eq_smoothExt` has been given a conflict-free import list.
/-!
# `Work.Diff.EXT.chartBounds_of_shibounds`

The step "Shi's a priori estimates + metric equivalence ⟹ uniform `C^k` bounds for the chart
matrices of the flow, together with a uniform lower bound for the metrics on `[T/2,T)`".

## The statement

`ChartBounds G (T/2) T` says that in the chart at every point, the chart matrix `y ↦ chartMat G x₀ t y`
is uniformly `C^k`-bounded for every `k`, uniformly for `t ∈ [T/2,T)`.

## Route

## The remaining chain (pieces in sibling modules)

The proof of `ChartBounds` is assembled from the following *delegated* pieces, all of which are
statements about objects *smaller* than the conclusion (the connection difference, the Ricci
tensor, or a finite-dimensional packaging step), plus the induction carried out below.

* `Work.Diff.EXT.covKRmExt_tensorial` (proved): the iterated covariant derivatives of the curvature
  are tensorial (they depend only on the point values of their arguments).
* `Work.Diff.EXT.covKRmExt_eval_bound` (in flight): the evaluation of `∇^k Rm` is bounded by
  `√(curvNormK · k)` times the product of the norms of the arguments — this is how the hypothesis
  `ShiBounds` is converted into a *tensor-norm* bound at every order.
* `Work.Diff.EXT.conn_diff_bound_of_shibounds` (in flight): `∇^{G(t)} - ∇^{G(0)}` is a bounded
  tensor on `[T/2,T)` (integration in `t` of the first variation of the Levi-Civita connection,
  `Work.Diff.T.lc_variation`, using `ShiBounds` at order `1`).
* `Work.Diff.EXT.conn_diff_cov_bounds` (in flight): every covariant derivative (with respect to the
  fixed connection `∇^{G(0)}`) of the connection difference stays bounded on `[T/2,T)`.  **The
  curvature-difference identity `R(G(t)) = R(G(0)) + ∇^{0}A + A ⋆ A` is *not* sufficient for this**
  (it pins down only the antisymmetrisation of `∇^{0}A` in its two derivative slots, so it cannot
  produce the `A`-tower bounds): the missing equation is the *time evolution*
  `∂_t (∇^{0,k}A) = ∇^{0,k}(∂_t A)`, whose right-hand side is the first-variation tensor of
  `Work.Diff.T.lc_variation` — see the "CORRECTION" section at the end of
  `Submission/Work/Diff/EXT/ATower/PLAN.md` for the full route.
* `Work.Diff.EXT.ATower.step_flip` (**proved**): changing the connection in one step of the tower
  recursion only inserts the value of the connection difference into the slots.
* **Status (2026-09-30 18:30).**  Everything in the chain below is proved except the `A`-tower
  bound itself, whose real content is `Submission/Work/Diff/EXT/ConnCov/covKAExt_bound.lean`
  (identical statement to `conn_diff_cov_bounds`); `#print axioms Work.Diff.EXT.chartBounds_of_shibounds`
  is consequently `[propext, sorryAx, Classical.choice, Quot.sound]` with that single `sorryAx`
  source.  `gram_data_bounds_v2`, `ATower/step_flip` and `dRmNormSq_bound_slab` were completed in
  this session.
* `Work.Diff.EXT.conn_diff_cov_bounds_v2` (in flight): same claim as `conn_diff_cov_bounds`, stated
  under a fresh name so that it can be proved on the route of the `PLAN.md` correction (time
  evolution of the tower + `step_flip` telescoping) without waiting for the original name.
* `Work.Diff.EXT.conn_diff_bound_sigma` (in flight): the `k = 0` case of the above on a general
  interval `[σ,T)`, `σ > 0`; stated separately because the `T/2`-version
  (`conn_diff_bound_of_shibounds`) goes through the small-time bound `dRmNormSq_bound_slab` and hence
  (via `curvNormK_jointSmooth`, `covK_boundaryExt`) currently carries `sorryAx`.
* `Work.Diff.EXT.aCovArr_eq_covKAExt` and `Work.Diff.EXT.covKAExt_frame_eq_smoothExt` (in flight):
  the *chart* recursion `aCovArr` (background Christoffel symbols `cGam (G 0)`) computes the same
  numbers as the field-level recursion `covKAExt` — this bridges the chart to the tensor bounds.
* `Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound`, `Work.Diff.EXT.gram_data_bounds_v2` (in flight):
  the fixed background data (`cGam (G 0)`, `GramM`, `GramInv` of `G t` versus `G 0`) is bounded on a
  compact chart set, with all its chart derivatives.
* `Work.Diff.EXT.chartMat_fderiv_basis` (in flight): the first chart derivative of the metric
  components is `∂_m u_{ij} = Σ_p (Γ^p_{mi} u_{pj} + Γ^p_{mj} u_{ip})` (metric compatibility).
* `Work.Diff.EXT.chartBounds_of_componentwise` (in flight): the finite-dimensional step from
  componentwise `C^k` bounds to the operator-norm bounds of `ChartBounds`.


### Status and the shape of the remaining induction (updated)

Proved and importable (all in this directory):

* `covKRmExt_tensorial`, `aCovArr_eq_covKAExt`, `chartMat_fderiv_basis`, `chartData_contDiffOn`,
  `cGam_zero_iteratedFDeriv_bound`, `norm_iteratedFDeriv_le_basisSum`,
  `chartBounds_of_componentwise`, `conn_diff_bound_of_shibounds`.

Still to be supplied by the fleet: `covKRmExt_eval_bound`, `conn_diff_cov_bounds`,
`covKAExt_tensorial`, `covKAExt_frame_eq_smoothExt`, `gram_data_bounds_v2`, `gram_det_bound`,
`christoffel_bounds_of_core`, `gramInv_bounds_of_gram_bounds`,
`chartMat_bounds_of_christoffel_bounds`.

**Warning about the shape of the last three.** They are stated *uniformly in all orders* `k`
("`∀ k` bounds in, `∀ k` bounds out"), and the three of them are *cyclic* at that granularity:
`gramInv_bounds_of_gram_bounds` needs the chart-matrix bounds, `christoffel_bounds_of_core` needs
the inverse-Gram bounds, and `chartMat_bounds_of_christoffel_bounds` needs the Christoffel bounds.
They cannot be combined as they stand.  The triangular order needed is *by order*:

  `P k` (chart matrix, order `k`)  →  `R k` (inverse Gram, order `k`)  →
  `Q k` (Christoffel data, order `k`)  →  `P (k+1)`,

where `R k` uses the determinant bound and the identity `GramInv = (GramM)⁻¹`, `Q k` uses
`Γ = Γ₀ + GramInv · aComp` and the `aCovArr` bounds, and `P (k+1)` uses the identity
`∂_m u_{ij} = Σ_p (Γ^p_{mi} u_{pj} + Γ^p_{mj} u_{ip})` plus the Leibniz inequality
`norm_iteratedFDeriv_mul_le` (via `ContDiffOn`/`UniqueDiffOn`).  Either the three lemmas above
should be restated with a fixed order `k` and then assembled by strong induction on `k`, or the
induction should be carried out directly here using their ingredients.

The induction carried out here is then the following, for a compact `K` inside the chart target:

* `P k`: the component functions `y ↦ chartMat G x₀ t y i j` have uniformly bounded `k`-th
  iterated derivatives on `K` (uniformly in `t ∈ [T/2,T)`);
* `Q k`: the (background) covariant derivatives of the connection difference have uniformly bounded
  `k`-th chart derivatives (this is the content of the `aCovArr` bounds, transported by the
  bridge lemmas above);
* `R k`: the inverse Gram matrix has uniformly bounded `k`-th iterated derivatives (from
  `P k` and the identity `GramInv * GramM = 1`).

`P (k+1)` follows by differentiating `∂_m u_{ij} = Σ_p (Γ^p_{mi} u_{pj} + Γ^p_{mj} u_{ip})` `k` times
(`Γ = Γ₀ + GramInv · aComp`) and using the Leibniz inequality
`norm_iteratedFDeriv_mul_le`; the terms are bounded by `Q (≤ k)`, `R (≤ k)` and `P (≤ k)`.

The nontrivial part is that *bounded geometric data does not bound the coordinate derivatives of the
metric*: the chart expression of a metric carries a "gauge" part that is invisible to the curvature
(two metrics with the same value, the same first derivatives and the same curvature at a point may
have different second derivatives).  In this workspace that is handled by the *connection difference*
`A(t) := ∇^{g(t)} - ∇^{g(0)}` of the flow with its own initial metric, whose *first* derivative vanishes:

* `A(0) = 0`, and its evolution is `∂ₜ A = ½ g⁻¹ (∇h + …)` with `h = ∂ₜ g = -2 Ric`; expressed in
  terms of the *tensorial* derivative `∇Ric` of the Ricci tensor this is a *bounded* quantity
  (bounded by `|∇Rm|` through `Work.Diff.EXT.ShiBounds`), so `A` is bounded on `[0,T)` by an
  integration in `t` — no maximum principle and no elliptic theory is needed;
* the curvature-difference identity `R(g(t)) = R(g(0)) + ∇^{0}A + A⋆A` (algebraic in `A` and the two
  curvatures) then bounds `∇^{0}A`, and differentiating it `j` times turns `∇^{0,{j+1}}A` into a
  polynomial in the *geometric* derivatives `∇^{g(t),i}Rm` of the curvature (which `ShiBounds`
  bounds, at every order) and in lower derivatives of `A`.  This is triangular and gives uniform
  bounds for all `∇^{0,j}A`;
* `∇^{0}g(t) = -2 sym A` and the fixed coordinate frame turn those tensorial bounds into bounds for
  the coordinate derivatives of the chart matrix.

This file is the assembly; the supporting pieces live in sibling modules.
-/


set_option linter.unusedSectionVars false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The metric equivalence gives a uniform lower bound on the second half of the flow.**
From `(G 0) ≤ e^{2nCt}(G t)` (for `t ∈ [0,T)`) one gets `e^{-2nCT}(G 0) ≤ (G t)` on `[T/2,T)`:
multiply by `e^{-2nCT}` and note that the remaining exponential factor is `≤ 1`. -/
theorem lower_bound_of_hmet
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) :
    ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
      a * (G 0).inner x u u ≤ (G t).inner x u u := by
  refine ⟨Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * T)), Real.exp_pos _, ?_⟩
  intro t ht x u
  -- the metric `G t` is positive semidefinite
  have hnonneg : 0 ≤ (G t).inner x u u := by
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    have h2 : (G t).inner x u u = ‖u‖ ^ 2 := by
      rw [show (G t).inner x u u = Inner.inner ℝ u u from rfl, real_inner_self_eq_norm_sq]
    rw [h2]; positivity
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := by rw [hn]; positivity
  have hnC : 0 ≤ n * C := mul_nonneg hn0 hC
  have ht0 : 0 ≤ t := le_trans (by linarith [hT]) ht.1
  have htT : t < T := ht.2
  have hmem : t ∈ Set.Ico 0 T := ⟨ht0, htT⟩
  have h := (hmet t hmem x u).2
  -- multiply by the positive factor `e^{-2nCT}`
  have hApos : 0 < Real.exp (-(2 * (n * C) * T)) := Real.exp_pos _
  have h1 : Real.exp (-(2 * (n * C) * T)) * (G 0).inner x u u
      ≤ Real.exp (-(2 * (n * C) * T))
        * (Real.exp (2 * (n * C) * t) * (G t).inner x u u) :=
    mul_le_mul_of_nonneg_left h hApos.le
  refine le_trans h1 ?_
  -- `e^{-2nCT} * e^{2nCt} = e^{2nC(t-T)} ≤ 1`
  have hmul : Real.exp (-(2 * (n * C) * T)) * Real.exp (2 * (n * C) * t)
      = Real.exp (2 * (n * C) * (t - T)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hmul]
  refine mul_le_of_le_one_left hnonneg (Real.exp_le_one_iff.mpr ?_)
  have : t - T ≤ 0 := by linarith
  nlinarith [hnC, this]

/-- A positive radius whose closed ball around the chart coordinate of `x₀` lies in the chart
target (the target is open and contains that coordinate). -/
lemma exists_closedBall_subset_target [I.Boundaryless] [T2Space M] (x₀ : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall ((extChartAt I x₀) x₀) r ⊆ (extChartAt I x₀).target := by
  have hsrc : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]; exact mem_chart_source H x₀
  have hmem : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hsrc
  have hopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨ε / 2, by linarith, fun y hy => hsub ?_⟩
  exact Metric.closedBall_subset_ball (by linarith) hy

/-- **The induction.**  From the boundedness of the chart recursion of the connection difference
(`hcore`), the bounded chart Gram data (`hgram`), the bounded background Christoffel data (`hcGam`),
the smoothness of the chart data (`hsm`, `hsmM`) and the first-derivative identity (`hderiv`), the
component functions of the chart matrix have uniformly bounded `C^k` data on `K`. -/
theorem chartMat_component_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (hU : UniqueDiffOn ℝ K)
    (hcore : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |aCovArr (I := I) (M := M) G x₀ t k v i j l y| ≤ Ck)
    (hgram : ∃ c Cl : ℝ, 0 < c ∧ 0 ≤ Cl ∧ c ≤ Cl ∧
      ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
        c ≤ Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i i ∧
        |Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j| ≤ Cl ∧
        |Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) i j| ≤ Cl)
    (hdet : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det)
    (hcGam : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') l i j) y‖
        ≤ C)
    (hsm : ∀ t ∈ Set.Ico σ T, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (pt (I := I) x₀ y') l i j) K)
    (hsmM : ∀ t ∈ Set.Ico σ T, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) K)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m i
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) p j
              + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m j
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i p)) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
          y‖ ≤ C := by
  obtain ⟨c, Cl, hc, hCl, hcCl, hGram⟩ := hgram
  have hident : ∀ (t : ℝ) (y : E) (i j : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j
        = Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j := by
    intro t y i j
    rfl
  have hval : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ 0 (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
        y‖ ≤ Cl := by
    intro t ht y hy i j
    rw [norm_iteratedFDeriv_zero, hident t y i j]
    exact (hGram t ht y hy i j).2.1
  have hcum : ∀ k : ℕ, ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
          y‖ ≤ C := by
    intro k
    induction k with
    | zero =>
        intro m hm
        obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm
        exact ⟨Cl, hCl, hval⟩
    | succ k ih =>
        intro m hm
        rcases Nat.lt_or_eq_of_le hm with hlt | rfl
        · exact ih m (Nat.lt_succ_iff.mp hlt)
        · refine chartData_step (I := I) (M := M) (G := G) (σ := σ) (T := T) (x₀ := x₀) (K := K)
            hKt hU k ?_ ?_ hdet hsmM hsm hderiv ih
          · exact fun m _ => hcore m
          · exact fun m _ => hcGam m
  exact fun k => hcum k k le_rfl


/-- **The requested lemma**: `ShiBounds` plus the metric equivalence give the uniform chart bounds
on `[T/2,T)` and a uniform lower bound for the metrics on that interval.

The `ChartBounds` half is assembled from the sibling modules (see the module docstring).  For a chart
centre `x₀` we take the closed ball `closedBall y₀ r` inside the chart target (compact, for the
fixed-data bounds) and its interior `U = ball y₀ r` (open, hence `UniqueDiffOn ℝ U`, for the
triangular induction).  The bounds on the chart recursion `aCovArr` come from the field-level
`conn_diff_cov_bounds` (`∇^{G 0,k}A` bounded), transported first to the coordinate frame
(`covKAExt_frame_eq_smoothExt`), then to the chart (`aCovArr_eq_covKAExt`, i.e. `ka_main` applied to
the two linearity lemmas `KaLinD_holds`/`KaLinT_holds`), then converted with the Gram bounds. -/
theorem chartBounds_of_shibounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    Work.Diff.EXT.ChartBounds (I := I) (M := M) G (T / 2) T ∧
      ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u := by
  refine ⟨?_, lower_bound_of_hmet (I := I) (M := M) G T C hT hC hmet⟩
  intro x₀
  obtain ⟨r, hr, hrsub⟩ := exists_closedBall_subset_target (I := I) (M := M) x₀
  set y₀ : E := (extChartAt I x₀) x₀ with hy₀
  set U : Set E := Metric.ball y₀ r with hU
  have hUopen : IsOpen U := by rw [hU]; exact Metric.isOpen_ball
  have hUsubK : U ⊆ Metric.closedBall y₀ r := by
    rw [hU]; exact Metric.ball_subset_closedBall
  have hKc : IsCompact (Metric.closedBall y₀ r) := isCompact_closedBall y₀ r
  have hy₀U : y₀ ∈ U := by
    rw [hU, Metric.mem_ball, dist_self]; exact hr
  have hUtarget : U ⊆ (extChartAt I x₀).target := fun y hy => hrsub (hUsubK hy)
  -- ### the Gram data, on the compact closed ball, restricted to `U`
  obtain ⟨c, Cl, hc, hCl, hcCl, hGram⟩ :=
    gram_data_bounds_v2 (I := I) (M := M) G T C hT hC hmet x₀ (Metric.closedBall y₀ r) hKc hrsub
  have hgramU : ∃ c Cl : ℝ, 0 < c ∧ 0 ≤ Cl ∧ c ≤ Cl ∧
      ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U, ∀ (i j : Fin (Module.finrank ℝ E)),
        c ≤ Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i i ∧
        |Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j| ≤ Cl ∧
        |Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) i j| ≤ Cl :=
    ⟨c, Cl, hc, hCl, hcCl, fun t ht y hy => hGram t ht y (hUsubK hy)⟩
  obtain ⟨cdet, hcdet, hdet⟩ :=
    gram_det_bound (I := I) (M := M) G T C hT hC hmet x₀ (Metric.closedBall y₀ r) hKc hrsub
  have hdetU : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      c ≤ (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det :=
    ⟨cdet, hcdet, fun t ht y hy => hdet t ht y (hUsubK hy)⟩
  have hcGamU : ∀ k : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ y ∈ U,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y‖ ≤ C' := by
    intro k
    obtain ⟨C', hC'0, hC'⟩ := cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀
      (Metric.closedBall y₀ r) hKc hrsub k
    exact ⟨C', hC'0, fun y hy i j l => hC' y (hUsubK hy) i j l⟩
  -- ### smoothness of the chart data
  obtain ⟨hsmMcomp, hsmGcomp, -⟩ := chartData_contDiffOn (I := I) (M := M) G x₀ U hUtarget
  have hsmM : ∀ t ∈ Set.Ico (T / 2) T, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) U :=
    fun t _ i j => hsmMcomp t i j
  have hsmG : ∀ t ∈ Set.Ico (T / 2) T, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (pt (I := I) x₀ y') l i j) U :=
    fun t _ i j l => hsmGcomp t i j l
  have hderiv : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m i
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) p j
              + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m j
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i p) :=
    fun t _ y hy i j m => chartMat_fderiv_basis (I := I) (M := M) G x₀ t hy i j m
  -- ### the bounds on the chart recursion `aCovArr`
  have hcore : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t k v i j l y| ≤ Ck := by
    intro k
    obtain ⟨Ck, hCk0, hCk⟩ :=
      Work.Diff.EXT.ConnCov.covKAExt_bound_v2 (I := I) (M := M) hLC G T C hT hC hflow hbound hmet
        hShi k
    refine ⟨Ck * (Real.sqrt Cl) ^ (k + 3),
      mul_nonneg hCk0 (pow_nonneg (Real.sqrt_nonneg Cl) _), ?_⟩
    intro t ht y hy v i j l
    rw [Work.Diff.EXT.aCovArr_eq_covKAExt (I := I) (M := M) G x₀ t k v i j l (hUtarget hy)]
    rw [covKAExt_frame_eq_smoothExt (I := I) (M := M) hLC G t k x₀ (hUtarget hy) v i j l]
    have hx := hCk t ht (pt (I := I) x₀ y)
      (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ j (pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ l (pt (I := I) x₀ y))
    have hdiag : ∀ m : Fin (Module.finrank ℝ E), (G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y)) ≤ Cl := by
      intro m
      have h1 := (hGram t ht y (hUsubK hy) m m).2.1
      have h2 : Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) m m = (G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y)) := rfl
      rw [h2] at h1
      exact le_trans (le_abs_self _) h1
    have hsq : ∀ m : Fin (Module.finrank ℝ E), Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y))) ≤ Real.sqrt Cl :=
      fun m => Real.sqrt_le_sqrt (hdiag m)
    have hprod : Finset.univ.prod (fun s : Fin k => Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)))) ≤ (Real.sqrt Cl) ^ k := by
      have h := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun s : Fin k => Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y))))
        (g := fun _ : Fin k => Real.sqrt Cl)
        (fun a _ => Real.sqrt_nonneg _) (fun a _ => hsq (v a))
      simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
    have hCl0 : 0 ≤ Real.sqrt Cl := Real.sqrt_nonneg Cl
    have hk0 : 0 ≤ (Real.sqrt Cl) ^ k := pow_nonneg hCl0 k
    have hA : Ck * Finset.univ.prod (fun s : Fin k => Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)))) ≤ Ck * (Real.sqrt Cl) ^ k := mul_le_mul_of_nonneg_left hprod hCk0
    have hB : Ck * Finset.univ.prod (fun s : Fin k => Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)))) * Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))) ≤ Ck * (Real.sqrt Cl) ^ k * Real.sqrt Cl :=
      mul_le_mul hA (hsq i) (Real.sqrt_nonneg _) (mul_nonneg hCk0 hk0)
    have hC2 : Ck * Finset.univ.prod (fun s : Fin k => Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)))) * Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))) * Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ j (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ j (pt (I := I) x₀ y)))
        ≤ Ck * (Real.sqrt Cl) ^ k * Real.sqrt Cl * Real.sqrt Cl :=
      mul_le_mul hB (hsq j) (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg hCk0 hk0) hCl0)
    have hD : Ck * Finset.univ.prod (fun s : Fin k => Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ (v s) (pt (I := I) x₀ y)))) * Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))) * Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ j (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ j (pt (I := I) x₀ y))) * Real.sqrt ((G t).inner (pt (I := I) x₀ y) (Work.Diff.GE.cFrame (I := I) x₀ l (pt (I := I) x₀ y)) (Work.Diff.GE.cFrame (I := I) x₀ l (pt (I := I) x₀ y)))
        ≤ Ck * (Real.sqrt Cl) ^ k * Real.sqrt Cl * Real.sqrt Cl * Real.sqrt Cl :=
      mul_le_mul hC2 (hsq l) (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hCk0 hk0) hCl0) hCl0)
    refine le_trans hx (le_trans hD ?_)
    rw [pow_add]; exact le_of_eq (by ring)
  -- ### the triangular induction, then the finite-dimensional packaging
  have hcomp := chartMat_component_bounds (I := I) (M := M) G (T / 2) T x₀ U hUtarget
    hUopen.uniqueDiffOn hcore hgramU hdetU hcGamU hsmG hsmM hderiv
  have hsmMat : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y := by
    intro t ht y hy
    exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
      (hsmMcomp t i j).contDiffAt (hUopen.mem_nhds hy)))
  have hcb := chartBounds_of_componentwise (I := I) (M := M) G (T / 2) T x₀ U
    (by rw [hUopen.interior_eq]; exact hy₀U) hsmMat hcomp
  refine ⟨U, hUopen, ?_, fun k => ?_⟩
  · exact hy₀U
  · obtain ⟨C', hC'0, hC'⟩ := hcb k
    exact ⟨C', hC'0, fun t ht y hy => hC' t ht y (by rw [hUopen.interior_eq]; exact hy)⟩

end Work.Diff.EXT
