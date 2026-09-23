import Submission.CutPoint

/-!
# The cut-point step, modulo the local model of the exponential map

`InjAtLeast hmet p m` says that the global exponential map `GExp p` is injective on the ball of
radius `m` (Riemannian norm) in `T_pM`; if it fails beyond `m`, the classical cut-point analysis
produces **two distinct minimising geodesics from `p` to a common point**, both of length `m`.  This
is the input of Klingenberg's estimate `ℓ(p) ≤ 2 inj(p)` (Cheeger–Ebin, Lemma 5.6).

This file proves that step modulo the *local model* of `GExp` by the chart exponential map `expMap`
(which is a genuine `Chart`-local gadget in this library: it is defined as the time-one value of a
chart geodesic and is junk outside the (chart-dependent) set of vectors admitting such a geodesic).
The hypotheses that enter are exactly the local model facts:

* `hexp`: on the closed ball of radius `R`, `GExp p` agrees with `expMap`;
* `hcont`: `expMap` is continuous there;
* `hnotloc`: `expMap` is *locally injective* there — supplied below Riemannian length `π/2` by
  Rauch's theorem (`CutPoint.forall_not_locally_injective_of_norm_lt_pi_half`, packaged as
  `exists_radius_not_locally_injective` below, which turns the Riemannian-length condition into a
  model-norm condition by the chart bounds);
* `hball`: the Riemannian ball of radius `m + 1` is contained in the model ball of radius `R`
  (the two norms are compared by the chart bounds, whose *existence* is all this needs).

Of these, `hnotloc` is a *theorem* (Rauch) rather than an assumption: see
`exists_radius_not_locally_injective`.

See `Submission/Roadmap.lean` §71–§72 for the discussion of why these hypotheses cannot (yet) be
discharged, and what is missing (a global smooth exponential map).

## Contents

* `sqrt_chartGram_eq_norm`, `sqrt_chartGram_add_le`: the Riemannian norm of a model vector at the
  base point, expressed through `chartGram`, and the triangle inequality for it;
* `exists_radius_not_locally_injective`: Rauch's theorem in the form "the chart exponential map is
  locally injective on a ball of the *model* space";
* `exists_two_minimising_of_not_injAtLeast`: the cut-point step.  Its hypothesis `hnotloc` on the
  ball of radius `R` is discharged by `exists_radius_not_locally_injective` as soon as `R` is at
  most the radius produced there (take the minimum of the three radii: agreement/continuity,
  local injectivity, and the containment `hball`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
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
open Submission.CutPoint

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CutStep

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The Riemannian norm of a model vector at the base point**, as an explicit expression.  For
`w : T_pM`, `√(chartGram p p w w)` is the Riemannian (fibre) norm of `w`. -/
lemma sqrt_chartGram_eq_norm (p : M) (w : TangentSpace I p) :
    Real.sqrt (chartGram (I := I) p p (w : E) (w : E)) = ‖w‖ := by
  rw [Submission.Distance.chartGram_self_apply (I := I) p (w : E) (w : E),
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]

/-- **The triangle inequality for `√(chartGram p p · ·)`** — the Riemannian norm at the base point,
read on the model space `E`. -/
lemma sqrt_chartGram_add_le (p : M) (a b : E) :
    Real.sqrt (chartGram (I := I) p p (a + b) (a + b))
      ≤ Real.sqrt (chartGram (I := I) p p a a) + Real.sqrt (chartGram (I := I) p p b b) := by
  have hsum : (show TangentSpace I p from (a + b))
      = (show TangentSpace I p from a) + (show TangentSpace I p from b) := rfl
  have h1 : Real.sqrt (chartGram (I := I) p p (a + b) (a + b))
      = ‖(show TangentSpace I p from (a + b))‖ := by
    rw [Submission.Distance.chartGram_self_apply (I := I) p (a + b) (a + b),
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h2 : Real.sqrt (chartGram (I := I) p p a a)
      = ‖(show TangentSpace I p from a)‖ := by
    rw [Submission.Distance.chartGram_self_apply (I := I) p a a,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h3 : Real.sqrt (chartGram (I := I) p p b b)
      = ‖(show TangentSpace I p from b)‖ := by
    rw [Submission.Distance.chartGram_self_apply (I := I) p b b,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, h2, h3]
  exact norm_add_le _ _

/-- **The chart exponential map is locally injective on a ball of the model space.**  This is
Rauch's theorem in the form `forall_not_locally_injective_of_norm_lt_pi_half` (no non-trivial Jacobi
field vanishing at both ends below Riemannian length `π/2`, i.e. no conjugate point below the
conjugate radius `π/2`) combined with the chart bounds at the base point: the Riemannian length of
`w` is at most `√Lam · ‖w‖`, so a *model*-norm ball of sufficiently small radius lies inside the
region where the exponential map is conjugacy-free.  The case `w = 0` is the inverse function
theorem at the origin (`mfderiv_expMap_zero`). -/
theorem exists_radius_not_locally_injective
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : E, ‖w‖ < R →
      ¬ (∀ ε : ℝ, 0 < ε → ∃ y z : E, ‖y - w‖ < ε ∧ ‖z - w‖ < ε ∧ y ≠ z ∧
          expMap cov p y = expMap cov p z) := by
  obtain ⟨ρ, hρ, hρlem⟩ :=
    CutPoint.forall_not_locally_injective_of_norm_lt_pi_half (cov := cov) htor hmet hpinch p
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) p
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H p)
  obtain ⟨ρ₂, hρ₂, hsm⟩ := Submission.Geodesic.exists_radius_contMDiffAt_expMap (cov := cov) p
  have hΛ : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hLam
  refine ⟨min ρ (min ρ₂ (Real.pi / (2 * Real.sqrt Lam))),
    lt_min hρ (lt_min hρ₂ (by positivity)), fun w hw hloc => ?_⟩
  have hwρ : ‖w‖ < ρ := lt_of_lt_of_le hw (min_le_left _ _)
  have hwρ₂ : ‖w‖ < ρ₂ := lt_of_lt_of_le hw (le_trans (min_le_right _ _) (min_le_left _ _))
  have hwπ : ‖w‖ < Real.pi / (2 * Real.sqrt Lam) :=
    lt_of_lt_of_le hw (le_trans (min_le_right _ _) (min_le_right _ _))
  by_cases hw0 : w = 0
  · -- the inverse function theorem at the origin
    subst hw0
    have hC1 : ContMDiffAt 𝓘(ℝ, E) I 1 (fun z : E => expMap cov p z) 0 :=
      (hsm 0 (by simpa using hρ₂)).of_le (by norm_num)
    obtain ⟨ε, hε, hinj⟩ :=
      Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv hC1
        (by rw [Submission.Geodesic.mfderiv_expMap_zero]; exact Function.injective_id)
    obtain ⟨y, z, hy, hz, hyz, heq⟩ := hloc ε hε
    exact hyz (hinj y z (by simpa using hy) (by simpa using hz) heq)
  · -- Rauch's theorem below the conjugate radius
    have hfib : Real.sqrt (chartGram (I := I) p p w w) < Real.pi / 2 := by
      have h1 : chartGram (I := I) p p w w ≤ Lam * ((fun z : E => ‖z‖) w) ^ 2 :=
        (hbnd p (by simp) w).2
      calc Real.sqrt (chartGram (I := I) p p w w)
          ≤ Real.sqrt (Lam * ((fun z : E => ‖z‖) w) ^ 2) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt Lam * (fun z : E => ‖z‖) w := by
            rw [Real.sqrt_mul hLam.le,
              Real.sqrt_sq (show (0 : ℝ) ≤ (fun z : E => ‖z‖) w from norm_nonneg _)]
        _ < Real.sqrt Lam * (Real.pi / (2 * Real.sqrt Lam)) :=
            mul_lt_mul_of_pos_left hwπ hΛ
        _ = Real.pi / 2 := by field_simp
    exact hρlem w hw0 hfib hwρ hloc

/-- **The cut-point step.**  Let `m > 0` be the injectivity radius at `p`: the exponential map is
injective on the Riemannian ball of radius `m` and not injective beyond it.  Assume moreover that
the chart exponential map at `p` is a good local model of `GExp p` on the ball of radius `R` (as
described in the module docstring).  Then there are two **distinct minimising vectors of length
`m`** with the same image:

* `u ≠ v` in `T_pM`, `GExp p u = GExp p v`, `‖u‖ = ‖v‖ = m`, and `d(p, GExp p u) = m`.

These are the two minimising geodesics of Klingenberg's lemma at the nearest cut point. -/
theorem exists_two_minimising_of_not_injAtLeast
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m R : ℝ} (hm : 0 < m) (hR : 0 < R)
    (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hexp : ∀ w : E, ‖w‖ ≤ R → GExp (cov := cov) hmet p w = expMap cov p w)
    (hcont : ContinuousOn (fun w : E => expMap cov p w) (Metric.closedBall (0 : E) R))
    (hnotloc : ∀ w : E, ‖w‖ < R → ¬ (∀ ε : ℝ, 0 < ε → ∃ y z : E,
        ‖y - w‖ < ε ∧ ‖z - w‖ < ε ∧ y ≠ z ∧ expMap cov p y = expMap cov p z))
    (hball : ∀ w : E, Real.sqrt (chartGram (I := I) p p w w) ≤ m + 1 → ‖w‖ < R) :
    ∃ u v : TangentSpace I p, u ≠ v ∧ GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m := by
  classical
  -- the chart bounds at the base point: the model norm controls the Riemannian norm
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) p
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H p)
  have hconv : ∀ a : E, Real.sqrt (chartGram (I := I) p p a a)
      ≤ Real.sqrt Lam * (fun z : E => ‖z‖) a := by
    intro a
    have h1 : chartGram (I := I) p p a a ≤ Lam * ((fun z : E => ‖z‖) a) ^ 2 := (hbnd p (by simp) a).2
    calc Real.sqrt (chartGram (I := I) p p a a)
        ≤ Real.sqrt (Lam * ((fun z : E => ‖z‖) a) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt Lam * (fun z : E => ‖z‖) a := by
          rw [Real.sqrt_mul hLam.le,
            Real.sqrt_sq (show (0 : ℝ) ≤ (fun z : E => ‖z‖) a from norm_nonneg _)]
  -- witness pairs with Riemannian norms `< m + 1/(n+1)`
  have hwit : ∀ n : ℕ, ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      ‖u‖ < m + 1 / ((n : ℝ) + 1) ∧ ‖v‖ < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : m < m + 1 / ((n : ℝ) + 1) := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    by_contra hcon
    push Not at hcon
    refine hfail (m + 1 / ((n : ℝ) + 1)) hpos (fun u v hu hv hG => ?_)
    by_contra huv
    exact absurd hv (not_lt.mpr (hcon u v huv hG hu))
  choose U V hUV using hwit
  -- the model-norm bounds
  have hhalf : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    linarith
  have hUb : ∀ n : ℕ, (fun z : E => ‖z‖) (U n) < R := by
    intro n
    refine hball (U n) ?_
    rw [sqrt_chartGram_eq_norm (I := I) p (U n)]
    linarith [(hUV n).2.2.1, hhalf n]
  have hVb : ∀ n : ℕ, (fun z : E => ‖z‖) (V n) < R := by
    intro n
    refine hball (V n) ?_
    rw [sqrt_chartGram_eq_norm (I := I) p (V n)]
    linarith [(hUV n).2.2.2, hhalf n]
  -- compactness in the model ball
  have hmem : ∀ n : ℕ, ((U n : E), (V n : E)) ∈
      Metric.closedBall (0 : E) R ×ˢ Metric.closedBall (0 : E) R := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact (hUb n).le
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact (hVb n).le
  obtain ⟨a, ha, φ, hφ, htend⟩ :=
    ((isCompact_closedBall (0 : E) R).prod (isCompact_closedBall (0 : E) R)).tendsto_subseq hmem
  have htu : Tendsto (fun n : ℕ => (show E from U (φ n))) atTop (𝓝 a.1) := by
    have h := (continuous_fst.tendsto a).comp htend
    simpa [Function.comp_def] using h
  have htv : Tendsto (fun n : ℕ => (show E from V (φ n))) atTop (𝓝 a.2) := by
    have h := (continuous_snd.tendsto a).comp htend
    simpa [Function.comp_def] using h
  -- the limits have Riemannian norm `≤ m`
  have hbd : ∀ n : ℕ, 1 / (((φ n : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    have h : (n : ℝ) ≤ ((φ n : ℕ) : ℝ) := by exact_mod_cast hφ.id_le n
    linarith
  have hfibU : ∀ n : ℕ, Real.sqrt (chartGram (I := I) p p (U (φ n)) (U (φ n)))
      ≤ m + 1 / ((n : ℝ) + 1) := fun n => le_trans
        ((sqrt_chartGram_eq_norm (I := I) p (U (φ n))).trans_le ((hUV (φ n)).2.2.1).le)
        (by linarith [hbd n])
  have hfibV : ∀ n : ℕ, Real.sqrt (chartGram (I := I) p p (V (φ n)) (V (φ n)))
      ≤ m + 1 / ((n : ℝ) + 1) := fun n => le_trans
        ((sqrt_chartGram_eq_norm (I := I) p (V (φ n))).trans_le ((hUV (φ n)).2.2.2).le)
        (by linarith [hbd n])
  have hlim0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hdist1 : Tendsto (fun n : ℕ => (fun z : E => ‖z‖) (a.1 - (show E from U (φ n)))) atTop (𝓝 0) := by
    have h := (htu.sub (tendsto_const_nhds (x := a.1))).norm
    have h' : Tendsto (fun n : ℕ => (fun z : E => ‖z‖) (a.1 - (show E from U (φ n)))) atTop (𝓝 0) := by
      simpa [Function.comp_def, norm_sub_rev] using h
    exact h'
  have hfib_u : Real.sqrt (chartGram (I := I) p p a.1 a.1) ≤ m := by
    have hlim : Tendsto (fun n : ℕ => Real.sqrt Lam * (fun z : E => ‖z‖) (a.1 - (show E from U (φ n)))
        + (m + 1 / ((n : ℝ) + 1))) atTop (𝓝 m) := by
      have h := ((tendsto_const_nhds (x := Real.sqrt Lam)).mul hdist1).add
        ((tendsto_const_nhds (x := m)).add hlim0)
      simpa using h
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => ?_)
    have htri := sqrt_chartGram_add_le (I := I) p (a.1 - (show E from U (φ n))) (show E from U (φ n))
    rw [sub_add_cancel] at htri
    linarith [htri, hconv (a.1 - (show E from U (φ n))), hfibU n]
  have hfib_v : Real.sqrt (chartGram (I := I) p p a.2 a.2) ≤ m := by
    have hlim : Tendsto (fun n : ℕ => Real.sqrt Lam * (fun z : E => ‖z‖) (a.2 - (show E from V (φ n)))
        + (m + 1 / ((n : ℝ) + 1))) atTop (𝓝 m) := by
      have hdist2 : Tendsto (fun n : ℕ => (fun z : E => ‖z‖) (a.2 - (show E from V (φ n)))) atTop (𝓝 0) := by
        have h := (htv.sub (tendsto_const_nhds (x := a.2))).norm
        simpa [Function.comp_def, norm_sub_rev] using h
      have h := ((tendsto_const_nhds (x := Real.sqrt Lam)).mul hdist2).add
        ((tendsto_const_nhds (x := m)).add hlim0)
      simpa using h
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => ?_)
    have htri := sqrt_chartGram_add_le (I := I) p (a.2 - (show E from V (φ n))) (show E from V (φ n))
    rw [sub_add_cancel] at htri
    linarith [htri, hconv (a.2 - (show E from V (φ n))), hfibV n]
  have haR : (fun z : E => ‖z‖) a.1 < R :=
    hball a.1 (le_trans hfib_u (by linarith))
  have haR' : (fun z : E => ‖z‖) a.2 < R :=
    hball a.2 (le_trans hfib_v (by linarith))
  -- agreement of `GExp` and `expMap` at the limits and along the sequence
  have hexpU : ∀ n : ℕ, expMap cov p (U (φ n)) = GExp (cov := cov) hmet p (U (φ n)) :=
    fun n => (hexp (U (φ n)) (le_of_lt (hUb (φ n)))).symm
  have hexpV : ∀ n : ℕ, expMap cov p (V (φ n)) = GExp (cov := cov) hmet p (V (φ n)) :=
    fun n => (hexp (V (φ n)) (le_of_lt (hVb (φ n)))).symm
  have hexpA1 : GExp (cov := cov) hmet p a.1 = expMap cov p a.1 := hexp a.1 haR.le
  have hexpA2 : GExp (cov := cov) hmet p a.2 = expMap cov p a.2 := hexp a.2 haR'.le
  have hcont1 : ContinuousAt (fun w : E => expMap cov p w) a.1 := by
    have hmem1 : a.1 ∈ Metric.ball (0 : E) R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact haR
    exact hcont.continuousAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem1)
      Metric.ball_subset_closedBall)
  have hcont2 : ContinuousAt (fun w : E => expMap cov p w) a.2 := by
    have hmem2 : a.2 ∈ Metric.ball (0 : E) R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact haR'
    exact hcont.continuousAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem2)
      Metric.ball_subset_closedBall)
  have hseq : ∀ n : ℕ, expMap cov p (U (φ n)) = expMap cov p (V (φ n)) := by
    intro n
    rw [hexpU n, hexpV n]
    exact (hUV (φ n)).2.1
  have hexp_eq : expMap cov p a.1 = expMap cov p a.2 :=
    tendsto_nhds_unique (hcont1.tendsto.comp htu)
      ((hcont2.tendsto.comp htv).congr' (Eventually.of_forall fun n => (hseq n).symm))
  have hGuv : GExp (cov := cov) hmet p a.1 = GExp (cov := cov) hmet p a.2 := by
    rw [hexpA1, hexp_eq, hexpA2]
  -- the degenerate case is excluded by local injectivity
  have hne : a.1 ≠ a.2 := by
    intro hcon
    refine hnotloc a.1 haR (fun ε hε => ?_)
    have h1 : ∀ᶠ n : ℕ in atTop, (fun z : E => ‖z‖) ((show E from U (φ n)) - a.1) < ε := by
      have h : Tendsto (fun n : ℕ => (fun z : E => ‖z‖) ((show E from U (φ n)) - a.1)) atTop (𝓝 0) := by
        have hh := (htu.sub (tendsto_const_nhds (x := a.1))).norm
        simpa [Function.comp_def, norm_sub_rev] using hh
      exact h.eventually_lt_const hε
    have h2 : ∀ᶠ n : ℕ in atTop, (fun z : E => ‖z‖) ((show E from V (φ n)) - a.1) < ε := by
      have h : Tendsto (fun n : ℕ => (fun z : E => ‖z‖) ((show E from V (φ n)) - a.1)) atTop (𝓝 0) := by
        have hh := (htv.sub (tendsto_const_nhds (x := a.1))).norm
        rw [← hcon] at hh
        simpa [Function.comp_def] using hh
      exact h.eventually_lt_const hε
    have h3 : ∀ᶠ n : ℕ in atTop, (show E from U (φ n)) ≠ (show E from V (φ n)) :=
      Eventually.of_forall fun n => fun hEq => (hUV (φ n)).1 hEq
    obtain ⟨n, hn1, ⟨hn2, hn3⟩⟩ := (h1.and (h2.and h3)).exists
    exact ⟨(show E from U (φ n)), (show E from V (φ n)), hn1, hn2, hn3, hseq n⟩
  -- assemble
  have hfib_u' : ‖(show TangentSpace I p from a.1)‖ ≤ m := by
    rw [← sqrt_chartGram_eq_norm (I := I) p (show TangentSpace I p from a.1)]
    exact hfib_u
  have hfib_v' : ‖(show TangentSpace I p from a.2)‖ ≤ m := by
    rw [← sqrt_chartGram_eq_norm (I := I) p (show TangentSpace I p from a.2)]
    exact hfib_v
  have hne' : (show TangentSpace I p from a.1) ≠ (show TangentSpace I p from a.2) :=
    fun h => hne h
  obtain ⟨h1, h2, h3, -⟩ := norm_eq_and_minimising_of_witness_pair (cov := cov) hmet htor hinj
    hne' hGuv hfib_u' hfib_v'
  exact ⟨(show TangentSpace I p from a.1), (show TangentSpace I p from a.2), hne',
    hGuv, h1, h2, h3⟩

end

end Submission.CutStep
