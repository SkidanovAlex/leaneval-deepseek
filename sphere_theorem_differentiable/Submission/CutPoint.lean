import Submission.CutWitness
import Submission.InjRadius
import Submission.FlowJacobi
import Submission.RauchSpeed
import Submission.Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv

set_option backward.isDefEq.respectTransparency.types false

/-!
# The minimising witness of the exponential map: the dichotomy

`InjAtLeast hmet p r` fails exactly when there is a **witness pair** `u ≠ v` with
`GExp p u = GExp p v` and `max ‖u‖ ‖v‖ < r`.  The classical *cut point* analysis needs a witness
pair of **minimal** `max`-norm: this is the pair of two distinct minimising geodesics of equal
length that Klingenberg's lemma produces.

The set of witness pairs is *not* closed (the condition `u ≠ v` is open), so the infimum `ν` of
`max ‖·‖` over witness pairs need not be attained.  This file proves the dichotomy:

> either there **is** a witness pair of minimal `max`-norm (`ν` is attained), or the exponential
> map fails to be **locally injective** at some tangent vector.

The second alternative is the "degenerate" case (`uₙ ≠ vₙ → u` with `GExp uₙ = GExp vₙ`); together
with the fact that `exp` is a local diffeomorphism at non-conjugate vectors
(`Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv`) it produces a genuine
conjugate point, which Rauch's theorem excludes below the conjugate radius.  See
`Submission/Roadmap.lean` §70.

## Contents

* `exists_minWitness_or_not_locally_injective`: the dichotomy;
* `exists_ne_zero_mfderiv_eq_zero_of_not_injective`: a non-injective (continuous linear) derivative
  has a non-zero kernel vector — the form in which the second alternative is used.

## Conventions

Everything is phrased in the **model space** `E`: the tangent vectors at `p` are identified with
`E` through the chart, so that `‖·‖` is the model norm (the fibre norm of the Riemannian metric is
equivalent to it, with the constants of `ChartBounds.exists_chartGram_bounds`).  The hypothesis
`hexp` records that `GExp p` agrees with the *chart* exponential map `expMap cov p` on the closed
ball of radius `R`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.JacobiTensor
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.Distance
open Submission.GeodesicSpeed
open Submission.ConjPoint
open Submission.InjRadius
open Submission.CutWitness

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CutPoint

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The minimising-witness dichotomy.**  Let `u₀ ≠ v₀` be a witness pair with
`max ‖u₀‖ ‖v₀‖ < R`, and suppose that on the closed ball of radius `R` the global exponential map
`GExp p` agrees with the chart exponential map `expMap cov p`, which is continuous there.  Then
either

* there is a witness pair `(u,v)` whose `max ‖·‖` is **minimal** among all witness pairs, or
* the chart exponential map is **not locally injective** at some vector `w ∈ E`.

The second case is the degenerate one: a minimising sequence of witness pairs collapses to a single
vector, in which case `expMap` fails to be injective on every neighbourhood of that vector. -/
theorem exists_minWitness_or_not_locally_injective
    (hmet : IsMetricCompatible cov)
    {p : M} {R : ℝ} (hR : 0 < R)
    (hexp : ∀ w : E, ‖w‖ ≤ R → GExp (cov := cov) hmet p w = expMap cov p w)
    (hcont : ContinuousOn (fun w : E => expMap cov p w) (Metric.closedBall (0 : E) R))
    {u₀ v₀ : E} (huv : u₀ ≠ v₀)
    (hG : GExp (cov := cov) hmet p u₀ = GExp (cov := cov) hmet p v₀)
    (hb : max ‖u₀‖ ‖v₀‖ < R) :
    (∃ u v : E, u ≠ v ∧ GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      (∀ u' v' : E, u' ≠ v' → GExp (cov := cov) hmet p u' = GExp (cov := cov) hmet p v' →
        max ‖u‖ ‖v‖ ≤ max ‖u'‖ ‖v'‖))
    ∨ (∃ w : E, ‖w‖ < R ∧
        ∀ ε : ℝ, 0 < ε → ∃ y z : E, ‖y - w‖ < ε ∧ ‖z - w‖ < ε ∧ y ≠ z ∧
        expMap cov p y = expMap cov p z) := by
  classical
  set S : Set ℝ :=
    {m | ∃ u v : E, u ≠ v ∧ GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      max ‖u‖ ‖v‖ = m} with hS
  have hSne : S.Nonempty :=
    ⟨max ‖u₀‖ ‖v₀‖, by rw [hS]; exact ⟨u₀, v₀, huv, hG, rfl⟩⟩
  have hSnn : ∀ m ∈ S, 0 ≤ m := by
    intro m hm
    rw [hS] at hm
    obtain ⟨u, v, -, -, hmax⟩ := hm
    rw [← hmax]
    exact le_max_of_le_left (norm_nonneg u)
  have hbdd : BddBelow S := ⟨0, hSnn⟩
  set ν : ℝ := sInf S with hνdef
  have hνle : ν ≤ max ‖u₀‖ ‖v₀‖ := by
    rw [hνdef]
    exact csInf_le hbdd (by rw [hS]; exact ⟨u₀, v₀, huv, hG, rfl⟩)
  have hνlt : ν < R := lt_of_le_of_lt hνle hb
  -- approximate minimisers
  have happrox : ∀ ε > 0, ∃ m ∈ S, m < ν + ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hle : ν + ε ≤ ν := by
      rw [hνdef]
      exact le_csInf hSne hcon
    linarith
  -- the minimising sequence
  have hseq : ∀ n : ℕ, ∃ q : E × E, q.1 ≠ q.2 ∧
      GExp (cov := cov) hmet p q.1 = GExp (cov := cov) hmet p q.2 ∧
      max ‖q.1‖ ‖q.2‖ < ν + min (1 / ((n : ℝ) + 1)) (R - ν) := by
    intro n
    have hε : 0 < min (1 / ((n : ℝ) + 1)) (R - ν) :=
      lt_min (by positivity) (sub_pos.mpr hνlt)
    obtain ⟨m, hmS, hmlt⟩ := happrox _ hε
    obtain ⟨u, v, huv, hG, hmax⟩ := hmS
    exact ⟨(u, v), huv, hG, by rw [hmax]; exact hmlt⟩
  choose q hq using hseq
  -- all the sequence elements lie in the ball of radius `R`
  have hqR : ∀ n : ℕ, ‖(q n).1‖ < R ∧ ‖(q n).2‖ < R := by
    intro n
    have h := (hq n).2.2
    have hmin : min (1 / ((n : ℝ) + 1)) (R - ν) ≤ R - ν := min_le_right _ _
    have hlt : max ‖(q n).1‖ ‖(q n).2‖ < R := by linarith
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hlt, lt_of_le_of_lt (le_max_right _ _) hlt⟩
  have hmem : ∀ n : ℕ, q n ∈
      Metric.closedBall (0 : E) R ×ˢ Metric.closedBall (0 : E) R := by
    intro n
    exact ⟨by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_lt (hqR n).1,
      by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_lt (hqR n).2⟩
  obtain ⟨a, ha, φ, hφ, htend⟩ :=
    ((isCompact_closedBall (0 : E) R).prod (isCompact_closedBall (0 : E) R)).tendsto_subseq hmem
  set u : E := a.1 with hudef
  set v : E := a.2 with hvdef
  have htu : Tendsto (fun n : ℕ => (q (φ n)).1) atTop (𝓝 u) := by
    have h := (continuous_fst.tendsto a).comp htend
    simpa [hudef, Function.comp_def] using h
  have htv : Tendsto (fun n : ℕ => (q (φ n)).2) atTop (𝓝 v) := by
    have h := (continuous_snd.tendsto a).comp htend
    simpa [hvdef, Function.comp_def] using h
  -- the limiting `max`-norm is at most `ν`
  have hlim_norm : Tendsto (fun n : ℕ => max ‖(q (φ n)).1‖ ‖(q (φ n)).2‖) atTop
      (𝓝 (max ‖u‖ ‖v‖)) :=
    htu.norm.max htv.norm
  have hlim_rhs : Tendsto (fun n : ℕ => ν + min (1 / ((φ n : ℝ) + 1)) (R - ν)) atTop (𝓝 ν) := by
    have hinf : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hinf
    have hmin : Tendsto (fun n : ℕ => min (1 / ((φ n : ℝ) + 1)) (R - ν)) atTop (𝓝 (min 0 (R - ν))) :=
      h0.min tendsto_const_nhds
    have hz : min (0 : ℝ) (R - ν) = 0 := min_eq_left (sub_nonneg.mpr hνlt.le)
    rw [hz] at hmin
    simpa using tendsto_const_nhds.add hmin
  have hνbound : max ‖u‖ ‖v‖ ≤ ν :=
    le_of_tendsto_of_tendsto' hlim_norm hlim_rhs (fun n => le_of_lt (hq (φ n)).2.2)
  have huR : ‖u‖ ≤ R := le_trans (le_max_left _ _) (le_trans hνbound hνlt.le)
  have hvR : ‖v‖ ≤ R := le_trans (le_max_right _ _) (le_trans hνbound hνlt.le)
  -- the two exponential maps agree at the limit
  have hexp_u : GExp (cov := cov) hmet p u = expMap cov p u := hexp u huR
  have hexp_v : GExp (cov := cov) hmet p v = expMap cov p v := hexp v hvR
  have hult : max ‖u‖ ‖v‖ < R := lt_of_le_of_lt hνbound hνlt
  have huint : u ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt (le_max_left _ _) hult
  have hvint : v ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt (le_max_right _ _) hult
  have hcu : ContinuousAt (fun w : E => expMap cov p w) u :=
    hcont.continuousAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds huint)
      Metric.ball_subset_closedBall)
  have hcv : ContinuousAt (fun w : E => expMap cov p w) v :=
    hcont.continuousAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hvint)
      Metric.ball_subset_closedBall)
  have hwitness : ∀ n : ℕ, expMap cov p ((q (φ n)).1) = expMap cov p ((q (φ n)).2) := by
    intro n
    have h1 : ‖(q (φ n)).1‖ ≤ R := (hqR (φ n)).1.le
    have h2 : ‖(q (φ n)).2‖ ≤ R := (hqR (φ n)).2.le
    rw [← hexp _ h1, ← hexp _ h2]
    exact (hq (φ n)).2.1
  have hGuv : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v := by
    rw [hexp_u, hexp_v]
    exact tendsto_nhds_unique ((hcu.tendsto.comp htu))
      ((hcv.tendsto.comp htv).congr' (Eventually.of_forall (fun n => (hwitness n).symm)))
  by_cases huv' : u = v
  · right
    refine ⟨u, lt_of_le_of_lt (le_max_left _ _) hult, fun ε hε => ?_⟩
    have h1 : ∀ᶠ n : ℕ in atTop, ‖(q (φ n)).1 - u‖ < ε := by
      have h0 : Tendsto (fun n : ℕ => ‖(q (φ n)).1 - u‖) atTop (𝓝 0) := by
        simpa using (htu.sub (tendsto_const_nhds (x := u))).norm
      exact h0.eventually_lt_const hε
    have h2 : ∀ᶠ n : ℕ in atTop, ‖(q (φ n)).2 - v‖ < ε := by
      have h0 : Tendsto (fun n : ℕ => ‖(q (φ n)).2 - v‖) atTop (𝓝 0) := by
        simpa using (htv.sub (tendsto_const_nhds (x := v))).norm
      exact h0.eventually_lt_const hε
    have h3 : ∀ᶠ n : ℕ in atTop, (q (φ n)).1 ≠ (q (φ n)).2 :=
      Eventually.of_forall fun n => (hq (φ n)).1
    obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and h3)).exists
    refine ⟨(q (φ n)).1, (q (φ n)).2, hn1, ?_, hn3, hwitness n⟩
    simpa [huv'] using hn2
  · left
    exact ⟨u, v, huv', hGuv, fun u' v' hu'v' hG' =>
      le_trans hνbound (csInf_le hbdd (by rw [hS]; exact ⟨u', v', hu'v', hG', rfl⟩))⟩



/-- **The minimising witness, with the degenerate branch excluded.**  If, in addition to the
hypotheses of `exists_minWitness_or_not_locally_injective`, the chart exponential map is locally
injective at every vector of model norm `< R` (this is the conclusion of
`forall_not_locally_injective_of_norm_lt_pi_half` on the region where the chart exponential map is
the correct model), then a witness pair of minimal `max`-norm exists — no degenerate case remains.

This is the form in which the cut-point step uses the dichotomy: the second alternative of
`exists_minWitness_or_not_locally_injective` is exactly "the exponential map is not locally
injective at a vector of norm `< R`", which Rauch's theorem excludes below Riemannian length
`π/2`. -/
theorem exists_minWitness_of_not_locally_injective
    (hmet : IsMetricCompatible cov)
    {p : M} {R : ℝ} (hR : 0 < R)
    (hexp : ∀ w : E, ‖w‖ ≤ R → GExp (cov := cov) hmet p w = expMap cov p w)
    (hcont : ContinuousOn (fun w : E => expMap cov p w) (Metric.closedBall (0 : E) R))
    (hnotloc : ∀ w : E, ‖w‖ < R → ¬ (∀ ε : ℝ, 0 < ε → ∃ y z : E, ‖y - w‖ < ε ∧ ‖z - w‖ < ε ∧
        y ≠ z ∧ expMap cov p y = expMap cov p z))
    {u₀ v₀ : E} (huv : u₀ ≠ v₀)
    (hG : GExp (cov := cov) hmet p u₀ = GExp (cov := cov) hmet p v₀)
    (hb : max ‖u₀‖ ‖v₀‖ < R) :
    ∃ u v : E, u ≠ v ∧ GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      (∀ u' v' : E, u' ≠ v' → GExp (cov := cov) hmet p u' = GExp (cov := cov) hmet p v' →
        max ‖u‖ ‖v‖ ≤ max ‖u'‖ ‖v'‖) := by
  rcases exists_minWitness_or_not_locally_injective (cov := cov) hmet hR hexp hcont huv hG hb with
    ⟨u, v, huv', hG', hmin⟩ | ⟨w, hwR, hw⟩
  · exact ⟨u, v, huv', hG', hmin⟩
  · exact absurd hw (hnotloc w hwR)

/-- **A non-injective derivative has a non-zero kernel vector.** -/
theorem exists_ne_zero_apply_eq_zero_of_not_injective {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E →L[ℝ] F} (h : ¬ Function.Injective f) :
    ∃ z : E, z ≠ 0 ∧ f z = 0 := by
  rw [Function.Injective] at h
  push Not at h
  obtain ⟨y, z, hyz, hyne⟩ := h
  refine ⟨y - z, sub_ne_zero.mpr hyne, ?_⟩
  rw [map_sub, hyz, sub_self]

/-- **A non-zero kernel vector of the differential of the exponential map makes the Jacobi tensor
singular.**  If `(mfderiv expMap v) w = 0` for a non-zero `w` and `‖v‖` is small, then the Jacobi
tensor `(Y,U)` of the chart geodesic with initial velocity `v` (`Y 0 = 0`, `U 0 = 1`, Jacobi system
on `Icc (-1) 1`) satisfies `(Y 1) w = 0`; in particular `Y 1` is not injective.

This is the first of the two bridges from the "degenerate" alternative of the minimising-witness
dichotomy to a conjugate point (see `Submission/Roadmap.lean` §70.5, (B1)). -/
theorem exists_jacobiTensor_singular_of_mfderiv_eq_zero (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ → ∀ w : E, w ≠ 0 →
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) w = 0 →
      ∃ (u ww : ℝ → E) (Y U : ℝ → E →L[ℝ] E),
        HasChartGeodesic cov x₀ v u ww ∧ Y 0 = 0 ∧ U 0 = 1 ∧ (Y 1) w = 0 ∧
        ¬ Function.Injective (Y 1) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u ww t).comp (Y t)) t) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt U (-((gammaOp (cov := cov) x₀ u ww t).comp (U t))
            - (curvOp (cov := cov) x₀ u ww t).comp (Y t)) t) := by
  obtain ⟨ρ, hρ, hdata⟩ :=
    Submission.FlowJacobi.exists_expMap_mfderiv_eq_jacobiTensor (cov := cov) htor x₀
  refine ⟨ρ, hρ, fun v hv w hw hzero => ?_⟩
  obtain ⟨u, ww, Y, U, hgc, hexp, hY0, hU0, hY, hU, hmf⟩ := hdata v hv w
  have hbase : expMap cov x₀ v ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) (x := x₀)]
    have h1 : expMap cov x₀ v = (extChartAt I x₀).symm (u 1) := by
      have h := hexp 1 (by norm_num)
      simpa using h
    rw [h1]
    exact (extChartAt I x₀).map_target (hgc.2.2.1 1 (by norm_num))
  have hYw : (Y 1) w = 0 := by
    have hzero' : frameVector (I := I) x₀ (expMap cov x₀ v) ((Y 1) w) = 0 := by
      rw [← hmf]
      exact hzero
    exact (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) hbase ((Y 1) w)).mp hzero'
  refine ⟨u, ww, Y, U, hgc, hY0, hU0, hYw, ?_, hY, hU⟩
  intro hinj
  exact hw (hinj (by rw [hYw, map_zero]))

/-- **The Jacobi tensor is injective at time `1` below Riemannian length `π/2`.**  This is Rauch's
theorem in the form needed for the minimal witness of the exponential map: along the chart geodesic
with initial velocity `v` of Riemannian norm `√⟨v,v⟩ < π/2`, the Jacobi tensor with `Y 0 = 0`,
`U 0 = 1` (whose columns are the Jacobi fields vanishing at `0`, i.e. the differential of the
exponential map) is injective at time `1`.

The Jacobi system is assumed on the interval `Icc (-(3/2)) (3/2)`, the shape in which
`FlowJacobi.exists_expMap_mfderiv_eq_jacobiTensor` produces it. -/
theorem jacobiTensor_injective_of_norm_lt_pi_half
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    {x₀ : M} {v : E} (hv0 : v ≠ 0)
    (hv : Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.pi / 2)
    {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    Function.Injective (Y 1) := by
  have hnn : 0 ≤ chartGram (I := I) x₀ x₀ v v := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
    positivity
  have hcpos : 0 < Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
    rw [Real.sqrt_pos]
    exact lt_of_le_of_ne hnn
      (fun h0 => hv0 ((chartGram_self_eq_zero_iff (mem_chart_source H x₀) v).mp h0.symm))
  have hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)
        = (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) ^ 2 := by
    intro t ht
    rw [hasChartGeodesic_chartGram_const hmet x₀ h t ht, Real.sq_sqrt hnn]
  refine Submission.RauchSpeed.jacobiTensor_injective_speed (cov := cov)
    (x₀ := x₀) (v := v) (u := u) (w := w) (A := -(3/2)) (B := 3/2) (t₁ := 1)
    (c := Real.sqrt (chartGram (I := I) x₀ x₀ v v))
    htor hmet hpinch h hcpos hspeed (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht => hY t ⟨ht.1.le, ht.2.le⟩) (fun t ht => hU t ⟨ht.1.le, ht.2.le⟩)
    hY0 hU0 (by norm_num) (by simpa using hv)

/-- **No singular Jacobi tensor at time `1` below Riemannian length `π/2`.**  The negation of the
conclusion of `jacobiTensor_injective_of_norm_lt_pi_half`, in the shape produced by the degenerate
branch of the minimising-witness dichotomy. -/
theorem not_exists_jacobiTensor_singular_of_norm_lt_pi_half
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    {x₀ : M} {v : E} (hv0 : v ≠ 0)
    (hv : Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.pi / 2) :
    ¬ ∃ (u w : ℝ → E) (Y U : ℝ → E →L[ℝ] E),
        HasChartGeodesic cov x₀ v u w ∧ Y 0 = 0 ∧ U 0 = 1 ∧ ¬ Function.Injective (Y 1) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
            - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  rintro ⟨u, w, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩
  exact hYinj (jacobiTensor_injective_of_norm_lt_pi_half (cov := cov) htor hmet hpinch
    hv0 hv hgc hY hU hY0 hU0)

/-- **A non-injective differential of the exponential map has a non-zero kernel vector** (in the
model space `E`; the subtraction is taken in `E`, which is where the instance search succeeds). -/
theorem exists_ne_zero_mfderiv_eq_zero_of_not_injective (x₀ : M) {v : E}
    (h : ¬ Function.Injective
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v)) :
    ∃ w : E, w ≠ 0 ∧ (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) w = 0 := by
  rw [Function.Injective] at h
  push Not at h
  obtain ⟨y, z, hyz, hyne⟩ := h
  refine ⟨(y : E) - (z : E), ?_, ?_⟩
  · intro hcon
    exact hyne (sub_eq_zero.mp hcon)
  · have hsub : (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) ((y : E) - (z : E))
        = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) y
          - (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) z :=
      map_sub _ _ _
    rw [hsub, hyz, sub_self]

/-- **The degenerate alternative of the dichotomy produces a singular Jacobi tensor.**
If the chart exponential map is not locally injective at `v` (with `‖v‖` small), then the Jacobi
tensor of the chart geodesic with initial velocity `v` is not injective at time `1`.

This combines the commons local-injectivity lemma with the two lemmas above: non-local-injectivity
gives a non-injective differential, hence a non-zero kernel vector, hence a non-injective `Y 1`. -/
theorem exists_jacobiTensor_singular_of_not_locally_injective (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ →
      (∀ ε : ℝ, 0 < ε → ∃ y z : E, ‖y - v‖ < ε ∧ ‖z - v‖ < ε ∧ y ≠ z ∧
        expMap cov x₀ y = expMap cov x₀ z) →
      ∃ (u ww : ℝ → E) (Y U : ℝ → E →L[ℝ] E),
        HasChartGeodesic cov x₀ v u ww ∧ Y 0 = 0 ∧ U 0 = 1 ∧ ¬ Function.Injective (Y 1) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u ww t).comp (Y t)) t) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt U (-((gammaOp (cov := cov) x₀ u ww t).comp (U t))
            - (curvOp (cov := cov) x₀ u ww t).comp (Y t)) t) := by
  obtain ⟨ρ₁, hρ₁, hdata⟩ := exists_jacobiTensor_singular_of_mfderiv_eq_zero (cov := cov) htor x₀
  obtain ⟨ρ₂, hρ₂, hsm⟩ := Submission.Geodesic.exists_radius_contMDiffAt_expMap (cov := cov) x₀
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun v hv hnot => ?_⟩
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < ρ₂ := lt_of_lt_of_le hv (min_le_right _ _)
  have hC1 : ContMDiffAt 𝓘(ℝ, E) I 1 (fun z : E => expMap cov x₀ z) v :=
    (hsm v hv2).of_le (by norm_num)
  have hnotinj : ¬ Function.Injective
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) := by
    intro hinj
    obtain ⟨ε, hε, hloc⟩ :=
      Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv hC1 hinj
    obtain ⟨y, z, hy, hz, hyz, heq⟩ := hnot ε hε
    exact hyz (hloc y z hy hz heq)
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_mfderiv_eq_zero_of_not_injective (cov := cov) x₀ hnotinj
  obtain ⟨u, ww, Y, U, hgc, hY0, hU0, -, hYinj, hY, hU⟩ := hdata v hv1 w hw0 hw
  exact ⟨u, ww, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩

/-- **The chart exponential map is locally injective at every vector of Riemannian norm `< π/2`.**
Contrapositive of the degenerate branch of the minimising-witness dichotomy, with the conjugate
point excluded by Rauch's theorem: if `√⟨v,v⟩ < π/2` and `‖v‖` is small enough that a chart
geodesic exists, then `expMap` is injective on some neighbourhood of `v`. -/
theorem forall_not_locally_injective_of_norm_lt_pi_half
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, v ≠ 0 →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.pi / 2 → ‖v‖ < ρ →
      ¬ (∀ ε : ℝ, 0 < ε → ∃ y z : E, ‖y - v‖ < ε ∧ ‖z - v‖ < ε ∧ y ≠ z ∧
          expMap cov x₀ y = expMap cov x₀ z) := by
  obtain ⟨ρ, hρ, hdata⟩ :=
    exists_jacobiTensor_singular_of_not_locally_injective (cov := cov) htor x₀
  refine ⟨ρ, hρ, fun v hv0 hv hvsmall hnot => ?_⟩
  obtain ⟨u, w, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩ := hdata v hvsmall hnot
  exact not_exists_jacobiTensor_singular_of_norm_lt_pi_half (cov := cov) htor hmet hpinch hv0 hv
    ⟨u, w, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩

/-- **A witness pair inside the injectivity ball consists of two minimising vectors of the same
length.**  If the exponential map at `p` is injective on the open ball of radius `m`, and `u ≠ v`
are two tangent vectors of norm `≤ m` with the same image, then

* both have norm exactly `m` (`u ≠ v` forces one of them to be outside the open injectivity ball),
  and
* both geodesic rays are **minimising** (`d(p, GExp p u) = ‖u‖`): a non-minimising ray would have
  failed earlier, at a time strictly below the injectivity radius.

This is the conclusion of the cut point analysis; the content that is *not* here is the production
of such a pair `(u,v)` from the failure of `InjAtLeast` (a compactness argument together with
continuity of `GExp p` at the limit — see `Submission/Roadmap.lean` §71). -/
theorem norm_eq_and_minimising_of_witness_pair
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    {u v : TangentSpace I p} (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v)
    (hu : ‖u‖ ≤ m) (hv : ‖v‖ ≤ m) :
    ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal m := by
  have key : ∀ w : TangentSpace I p, ‖w‖ ≤ m →
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p w) = ENNReal.ofReal ‖w‖ := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      rw [GExp_zero, Manifold.riemannianEDist_self, norm_zero, ENNReal.ofReal_zero]
    · by_contra hcon
      have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p w)
          < ENNReal.ofReal ‖w‖ :=
        lt_of_le_of_ne (Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet w) hcon
      set η : TangentSpace I p := unitOf w hw0 with hηdef
      have hη : ‖η‖ = 1 := unitOf_norm w hw0
      have hscale : ‖w‖ • η = w := by
        rw [hηdef]
        show ‖w‖ • unitOf w hw0 = w
        rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul]
      have hnot' : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖w‖ • η))
          < ENNReal.ofReal ‖w‖ := by rw [hscale]; exact hlt
      obtain ⟨s, hs, hslt⟩ := Submission.CutWitness.exists_lt_of_not_minimising_ray
        (cov := cov) hmet hη (norm_pos_iff.mpr hw0) hnot'
      have hsle : s < m := lt_of_lt_of_le hs.2 hw
      have hsn : ‖s • η‖ = s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hη, mul_one]
      have hηne : η ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hη
        norm_num at hη
      have hmin := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (cov := cov) hmet htor
        hinj (by rw [hsn]; exact lt_of_lt_of_le hs.2 hw)
        (smul_ne_zero hs.1.ne' hηne)
      rw [hsn] at hmin
      exact absurd hmin (ne_of_lt hslt)
  have hminu := key u hu
  have hminv := key v hv
  have heq : ENNReal.ofReal ‖u‖ = ENNReal.ofReal ‖v‖ := by rw [← hminu, hG, hminv]
  have hnorm : ‖u‖ = ‖v‖ := by
    have h := congrArg ENNReal.toReal heq
    rwa [ENNReal.toReal_ofReal (norm_nonneg u), ENNReal.toReal_ofReal (norm_nonneg v)] at h
  have hunorm : ‖u‖ = m := by
    refine le_antisymm hu ?_
    by_contra hcon
    push Not at hcon
    exact huv (hinj u v hcon (by rw [← hnorm]; exact hcon) hG)
  exact ⟨hunorm, by rw [← hnorm, hunorm], by rw [hminu, hunorm],
    by rw [hminv, ← hnorm, hunorm]⟩

/-- **The cut point step from a convergent witness sequence.**  If `(U n, V n)` are witness pairs
whose norms tend to `m` and converge to tangent vectors `u ≠ v`, and the exponential map is
continuous at `u` and `v`, then the metrics of the two rays are minimising and `‖u‖ = ‖v‖ = m`.

Everything is a hypothesis except the metric conclusion: what is missing for the injectivity radius
estimate is (i) the production of the convergent sequence (compactness of the closed ball of radius
`m + 1` around `p`, plus continuity of `GExp p` on it — see `Submission/Roadmap.lean` §71) and
(ii) the exclusion of the degenerate case `u = v` (which is where the conjugate point analysis of
`Submission.CutPoint` and Rauch's theorem are needed). -/
theorem norm_eq_and_minimising_of_witness_sequence
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    {U V : ℕ → TangentSpace I p} {u v : TangentSpace I p}
    (hb : ∀ n, ‖U n‖ < m + 1 / ((n : ℝ) + 1))
    (hb' : ∀ n, ‖V n‖ < m + 1 / ((n : ℝ) + 1))
    (hG : ∀ n, GExp (cov := cov) hmet p (U n) = GExp (cov := cov) hmet p (V n))
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v))
    (hcU : ContinuousAt (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) u)
    (hcV : ContinuousAt (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) v)
    (huv : u ≠ v) :
    ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 m) := by
    simpa using (tendsto_const_nhds (x := m)).add h0
  have hu : ‖u‖ ≤ m := le_of_tendsto_of_tendsto' hU.norm hlim (fun n => (hb n).le)
  have hv : ‖v‖ ≤ m := le_of_tendsto_of_tendsto' hV.norm hlim (fun n => (hb' n).le)
  have hGuv : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v :=
    tendsto_nhds_unique ((hcU.tendsto.comp hU))
      ((hcV.tendsto.comp hV).congr' (Eventually.of_forall fun n => (hG n).symm))
  obtain ⟨h1, h2, h3, -⟩ :=
    norm_eq_and_minimising_of_witness_pair (cov := cov) hmet htor hinj huv hGuv hu hv
  exact ⟨h1, h2, h3⟩

/-- **The compactness half of the cut-point step.**  If witness pairs exist with both norms
`< r` for every `r > m`, then there is a witness sequence `(U n, V n)` with both norms
`< m + 1/(n+1)` whose limits `u`, `v` have norm `≤ m`.

What is *not* here: the identification `GExp p u = GExp p v` (continuity of `GExp p` at the limits)
and the exclusion of the degenerate case `u = v` (see `Submission/Roadmap.lean` §71.2). -/
theorem exists_tendsto_witness_sequence
    (hmet : IsMetricCompatible cov) {p : M} {m : ℝ}
    (hex : ∀ r : ℝ, m < r → ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧ ‖u‖ < r ∧ ‖v‖ < r) :
    ∃ (U V : ℕ → TangentSpace I p) (u v : TangentSpace I p),
      (∀ n, U n ≠ V n) ∧
      (∀ n, GExp (cov := cov) hmet p (U n) = GExp (cov := cov) hmet p (V n)) ∧
      (∀ n, ‖U n‖ < m + 1 / ((n : ℝ) + 1)) ∧
      (∀ n, ‖V n‖ < m + 1 / ((n : ℝ) + 1)) ∧
      Tendsto U atTop (𝓝 u) ∧ Tendsto V atTop (𝓝 v) ∧ ‖u‖ ≤ m ∧ ‖v‖ ≤ m := by
  classical
  haveI hproper : ProperSpace (TangentSpace I p) := by
    haveI : FiniteDimensional ℝ (TangentSpace I p) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I p)
  have hstep : ∀ n : ℕ, ∃ q : TangentSpace I p × TangentSpace I p, q.1 ≠ q.2 ∧
      GExp (cov := cov) hmet p q.1 = GExp (cov := cov) hmet p q.2 ∧
      ‖q.1‖ < m + 1 / ((n : ℝ) + 1) ∧ ‖q.2‖ < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨u, v, huv, hG, hu, hv⟩ := hex (m + 1 / ((n : ℝ) + 1)) (by linarith)
    exact ⟨(u, v), huv, hG, hu, hv⟩
  choose q hq using hstep
  have hmem : ∀ n : ℕ, q n ∈ Metric.closedBall (0 : TangentSpace I p) (m + 1) ×ˢ
      Metric.closedBall (0 : TangentSpace I p) (m + 1) := by
    intro n
    have h1 : ‖(q n).1‖ ≤ m + 1 := by
      have := (hq n).2.2.1
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith
    have h2 : ‖(q n).2‖ ≤ m + 1 := by
      have := (hq n).2.2.2
      have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith
    exact ⟨by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact h1,
      by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact h2⟩
  obtain ⟨a, ha, φ, hφ, htend⟩ :=
    ((isCompact_closedBall (0 : TangentSpace I p) (m + 1)).prod
      (isCompact_closedBall (0 : TangentSpace I p) (m + 1))).tendsto_subseq hmem
  have hbd : ∀ n : ℕ, 1 / (((φ n : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    have h : (n : ℝ) ≤ ((φ n : ℕ) : ℝ) := by exact_mod_cast hφ.id_le n
    linarith
  have hbU : ∀ n, ‖(q (φ n)).1‖ < m + 1 / ((n : ℝ) + 1) :=
    fun n => lt_of_lt_of_le (hq (φ n)).2.2.1 (by linarith [hbd n])
  have hbV : ∀ n, ‖(q (φ n)).2‖ < m + 1 / ((n : ℝ) + 1) :=
    fun n => lt_of_lt_of_le (hq (φ n)).2.2.2 (by linarith [hbd n])
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 m) := by
    simpa using (tendsto_const_nhds (x := m)).add h0
  have htu : Tendsto (fun n : ℕ => (q (φ n)).1) atTop (𝓝 a.1) := by
    have h := (continuous_fst.tendsto a).comp htend
    simpa [Function.comp_def] using h
  have htv : Tendsto (fun n : ℕ => (q (φ n)).2) atTop (𝓝 a.2) := by
    have h := (continuous_snd.tendsto a).comp htend
    simpa [Function.comp_def] using h
  refine ⟨fun n => (q (φ n)).1, fun n => (q (φ n)).2, a.1, a.2, fun n => (hq (φ n)).1,
    fun n => (hq (φ n)).2.1, hbU, hbV, htu, htv,
    le_of_tendsto_of_tendsto' htu.norm hlim (fun n => (hbU n).le),
    le_of_tendsto_of_tendsto' htv.norm hlim (fun n => (hbV n).le)⟩

end

end Submission.CutPoint
