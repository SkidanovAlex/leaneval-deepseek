import Mathlib
import Submission.Work.OddBound.polygon.SegmentDomainEndpointDefs
import Submission.Work.OddBound.polygon.isConjugateTime_comp_sub
import Submission.Work.OddBound.polygon.minimiser_unique_of_mem_segmentDomain
import Submission.CutKlingenberg
import Submission.KlingenbergEven
import Submission.HopfRinow2

set_option backward.isDefEq.respectTransparency.types false

/-!
# The reversed velocity at the endpoint of a minimising ray lies in the segment domain

This module proves `Work.OddBound.polygon.segmentDomain_endpoint_revVelocity`, i.e. the `Prop`
`RevVelocityInSegmentDomain` of `SegmentDomainEndpointDefs`: for a unit vector `ξ` at `x₀`, a radius
`r` with `InjAtLeast hmet x₀ r`, and `0 < m < r`, the reversed velocity
`m • (-γ̇(m))` of the ray `γ s = GExp x₀ (s • ξ)` at the endpoint `y = γ m` lies in the tangential
segment domain `D̃_y`.

By `SegmentDomain.mem_segmentDomain_iff` this is the strict statement `m < cutTime y (-γ̇ m)`, i.e.
the classical symmetry of the cut locus along a single minimising geodesic: the reversed ray from
`y` keeps being minimising *strictly past* `x₀`.

The proof is the classical cut-point dichotomy (`σ ≤ κ`-free form):

* `m ≤ cutTime y (-γ̇ m)`: the reversed ray runs from `y` back to `x₀` in time `m`
  (`GExp_neg_velocity_of_ray`) and `d(y, x₀) = m` because the ray from `x₀` is minimising up to `r`;
* if `m = cutTime y (-γ̇ m)`, Klingenberg's dichotomy at the cut time
  (`exists_two_minimising_or_not_locallyInjective_of_cutTime_noinj`) gives either
  * a second minimising vector `v ≠ m • (-γ̇ m)` with `GExp y v = x₀`, `‖v‖ = m` — impossible by
    `curveVelocity_GExp_ray_one_eq_neg` (which identifies the *unique* such `v`), or
  * `GExp y` not locally injective at `m • (-γ̇ m)` — which forces a conjugate time at `m` along the
    reversed ray, hence (by `isConjugateTime_comp_sub`, i.e. `GExp y ((m - s) • (-γ̇ m)) = γ s`)
    a conjugate time at `m` along the ray of `ξ` from `x₀`, contradicting `InjAtLeast hmet x₀ r`.

-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open scoped ContDiff Manifold Topology ENNReal
open Bundle

namespace Work.OddBound.polygon

open scoped Bundle Topology
open ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## 1. Elementary facts about the ray -/

/-- The velocity of a unit `GExp`-ray is a unit vector. -/
theorem norm_curveVelocity_GExp_ray_eq_one
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m) :
    ‖Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m‖ = 1 := by
  have hξne : ξ ≠ 0 := by intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  rw [Submission.GlobalExp.norm_curveVelocity_GExp_smul (cov := cov) hmet x hξne hm, hξ]

/-- **Rescaling the ray.**  The velocity at time `1` of the ray with initial velocity `a • v` is `a`
times the velocity of the ray of `v` at time `a`. -/
theorem curveVelocity_ray_smul_one
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {x : M} {v : TangentSpace I x} {a : ℝ} (hv : v ≠ 0) :
    Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • (a • v))) 1
      = a • Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • v)) a := by
  have hfun : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • (a • v)))
      = (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((a * s + 0) • v)) := by
    funext s
    rw [smul_smul, show s * a = a * s + 0 from by ring]
  have hdiff : MDifferentiableAt 𝓘(ℝ) I
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • v)) (a * 1 + 0) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hv).mdifferentiableAt (by simp)
  rw [hfun, Submission.Length.curveVelocity_comp_mul_add (I := I)
    (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • v))
    (c := a) (d := 0) (t := 1) hdiff]
  rw [show a * 1 + 0 = a from by ring]

theorem unitOf_smul_neg_curveVelocity
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m)
    (hvne : m • (-Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m) ≠ 0) :
    Submission.GlobalExp.unitOf
        (m • (-Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m)) hvne
      = -Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m := by
  have hnorm : ‖m • (-Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m)‖ = m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm, Submission.InjRadiusCut.norm_neg_tangent,
      norm_curveVelocity_GExp_ray_eq_one (cov := cov) hmet hξ hm, mul_one]
  rw [Submission.GlobalExp.unitOf, hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hm), one_smul]

/-! ## 2. The reversed ray of a minimising ray, for all times -/

/-- **The reversed ray identity, for all parameters.**  If `q = GExp x (m • ξ)` is a point of the
unit ray of `ξ` and `w` is the velocity there, then the ray of `-w` from `q` is the reversal of the
ray of `ξ`: `GExp q (u • (-w)) = GExp x ((m - u) • ξ)` for **every** `u : ℝ`. -/
theorem GExp_neg_velocity_of_ray_all
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m) :
    ∀ u : ℝ, Submission.GlobalExp.GExp (cov := cov) hmet
        (Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ))
        (u • (-Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m))
      = Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ) := by
  have hξne : ξ ≠ 0 := by intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hray_sm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hξne
  have hray_geo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet x hξne t
  have hray_ne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t ≠ 0 :=
    fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet x hξne t
  have hsm : ContMDiff 𝓘(ℝ) I ∞ (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ)) :=
    hray_sm.comp (contMDiff_const.sub contMDiff_id)
  have hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov
      (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ)) t := by
    intro t
    have h1 : (-1 : ℝ) * t + m ∈ Set.Ioo ((-1 : ℝ) * t + m - 1) ((-1 : ℝ) * t + m + 1) :=
      ⟨by linarith, by linarith⟩
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov)
      (σ := fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (r • ξ))
      (c := (-1 : ℝ) * t + m - 1) (d := (-1 : ℝ) * t + m + 1) (a := -1) (b := m) (by norm_num)
      (hray_sm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hray_geo y) h1
    have h2 : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (((-1 : ℝ) * s + m) • ξ))
        = (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ)) := by
      funext s
      rw [show (-1 : ℝ) * s + m = m - s from by ring]
    rw [h2] at h
    exact h
  have hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ)) t ≠ 0 := by
    intro t
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) (t := m) (r := t)
      ((hray_sm (m - t)).mdifferentiableAt (by simp))]
    exact neg_ne_zero.mpr (hray_ne (m - t))
  have h0 : (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ)) 0
      = Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ) := by
    simp
  have hv : Submission.Geodesic.curveVelocity (I := I)
      (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ)) 0
      = -Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m := by
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) (t := m) (r := 0)
      ((hray_sm (m - 0)).mdifferentiableAt (by simp))]
    rw [show m - (0 : ℝ) = m from by ring]
  intro u
  have h := Submission.KlingenbergEven.eq_GExp_of_isGeodesicAt (cov := cov) hmet
    (q := Submission.GlobalExp.GExp (cov := cov) hmet x (m • ξ))
    (V := -Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) m)
    (neg_ne_zero.mpr (hray_ne m))
    (σ := fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x ((m - u) • ξ))
    hsm hgeo hne h0 hv u
  exact h.symm


/-! ## 3. The cut-point dichotomy, without the injectivity hypothesis -/

/-- **Klingenberg's dichotomy at a cut time, in its hypothesis-free form.**  Let `m > 0` be the cut
time of the unit direction `ξ` at `p` (`cutTime hmet p ξ = m`).  Then either there is a second
minimising vector `v ≠ m • ξ` of norm `m` with the same image as `m • ξ`, or `GExp p` fails to be
locally injective at `m • ξ`.

This is `Submission.CutKlingenberg.exists_two_minimising_or_not_locallyInjective_of_cutTime` without
the hypothesis `InjAtLeast hmet p m`: continuity of `GExp p` at the relevant points is available
unconditionally (`Submission.GExpLocalInj.contMDiffAt_GExp_one`), and the minimality of the cut
point follows from `cutTime p ξ = m` via `Submission.CutTime.mem_minimisingSet_iff`. -/
theorem exists_two_minimising_or_not_locallyInjective_of_cutTime_noinj
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m)
    (hτ : Submission.CutTime.cutTime (I := I) hmet p ξ = m) :
    (∃ v : TangentSpace I p, v ≠ m • ξ ∧ ‖v‖ = m ∧
      Submission.GlobalExp.GExp (cov := cov) hmet p v
        = Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ))
    ∨ ¬ Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p (m • ξ) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- the minimality of the cut point, from `cutTime p ξ = m`
  have hmin : Manifold.riemannianEDist I p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m :=
    ((Submission.CutTime.mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ).mpr
      ⟨hm.le, le_of_eq hτ.symm⟩).2
  -- continuity of `GExp p` at the points of the ray (unconditional)
  have hcontpt : ∀ z : TangentSpace I p, ContinuousAt
      (fun w : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p w) z :=
    fun z => (Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet p z).continuousAt
  set t : ℕ → ℝ := fun n => m + 1 / ((n : ℝ) + 1) with htdef
  have htpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have htgt : ∀ n : ℕ, m < t n := fun n => by
    have := htpos n
    rw [htdef]
    simp only
    linarith
  have htend : Tendsto t atTop (𝓝 m) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [htdef, add_zero] using (tendsto_const_nhds (x := m)).add h0
  -- the ray is not minimising at time `t n`
  have hnotmin : ∀ n : ℕ,
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))
        < ENNReal.ofReal (t n) := by
    intro n
    have h0 : 0 ≤ t n := (le_of_lt hm).trans (htgt n).le
    by_contra hcon
    have heq : Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ)) = ENNReal.ofReal (t n) :=
      le_antisymm (Submission.GExpRay.edist_GExp_smul_le_zero (cov := cov) hmet p hξ h0)
        (not_lt.mp hcon)
    have hmem : t n ∈ Submission.CutTime.minimisingSet (I := I) hmet p ξ := ⟨h0, heq⟩
    have hle : t n ≤ Submission.CutTime.cutTime (I := I) hmet p ξ :=
      ((Submission.CutTime.mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ).mp hmem).2
    rw [hτ] at hle
    linarith [htgt n]
  -- minimising vectors for the points of the ray
  have hwit : ∀ n : ℕ, ∃ v : TangentSpace I p,
      Submission.GlobalExp.GExp (cov := cov) hmet p v
        = Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ) ∧
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))
        = ENNReal.ofReal ‖v‖ ∧
      ‖v‖ < t n := by
    intro n
    obtain ⟨v, hv, hd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))
    refine ⟨v, hv, hd, ?_⟩
    have hd' : Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p v)
        = ENNReal.ofReal ‖v‖ := by
      rw [hv, hd]
    have hlt := hnotmin n
    rw [← hv, hd'] at hlt
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hlt).1
  choose v hvG hvd hvlt using hwit
  -- the exponential distances converge
  have hsm : Tendsto (fun n : ℕ => t n • ξ) atTop (𝓝 (m • ξ)) := htend.smul_const ξ
  have hraytend : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))
      atTop (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ))) :=
    (hcontpt (m • ξ)).tendsto.comp hsm
  have hlimedist : Tendsto
      (fun n : ℕ => Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))) atTop
      (𝓝 (ENNReal.ofReal m)) := by
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    have hcont : Continuous (fun y : M => edist p y) :=
      continuous_edist.comp (continuous_const.prodMk continuous_id)
    have h1 : Tendsto
        (fun n : ℕ => edist p (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))) atTop
        (𝓝 (edist p (Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ)))) :=
      hcont.continuousAt.tendsto.comp hraytend
    have h2 : edist p (Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m := by
      rw [Submission.EDist.edist_eq_riemannianEDist (I := I)]
      exact hmin
    rw [h2] at h1
    simpa only [Submission.EDist.edist_eq_riemannianEDist] using h1
  -- consequently the norms converge to `m`
  have hnormtend : Tendsto (fun n : ℕ => ‖v n‖) atTop (𝓝 m) := by
    have hfin : ∀ n : ℕ, Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ)) ≠ ⊤ :=
      fun n => (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p _).ne
    have h2 := (ENNReal.tendsto_toReal_iff hfin ENNReal.ofReal_ne_top).mpr hlimedist
    have h3 : Tendsto (fun n : ℕ =>
        (Manifold.riemannianEDist I p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))).toReal) atTop
        (𝓝 m) := by
      simpa only [ENNReal.toReal_ofReal hm.le] using h2
    have h4 : (fun n : ℕ => ‖v n‖)
        = fun n : ℕ =>
            (Manifold.riemannianEDist I p
              (Submission.GlobalExp.GExp (cov := cov) hmet p (t n • ξ))).toReal := by
      funext n
      rw [hvd n]
      exact (ENNReal.toReal_ofReal (norm_nonneg (v n))).symm
    rw [h4]
    exact h3
  -- boundedness and a convergent subsequence
  have hbound : ∀ n : ℕ, v n ∈ Metric.closedBall (0 : TangentSpace I p) (m + 1) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_of_lt ((hvlt n).trans_le ?_)
    rw [htdef]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  haveI hproper : ProperSpace (TangentSpace I p) := by
    haveI : FiniteDimensional ℝ (TangentSpace I p) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I p)
  obtain ⟨w, hwmem, φ, hφ, hwtend⟩ :=
    (isCompact_closedBall (0 : TangentSpace I p) (m + 1)).tendsto_subseq hbound
  have hw : ‖w‖ = m := by
    have h1 : Tendsto (fun n : ℕ => ‖v (φ n)‖) atTop (𝓝 ‖w‖) := hwtend.norm
    exact tendsto_nhds_unique h1 (hnormtend.comp hφ.tendsto_atTop)
  -- the limit maps to the same point
  have hGw : Submission.GlobalExp.GExp (cov := cov) hmet p w
      = Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ) := by
    have h1 : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (v (φ n)))
        atTop (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet p w)) :=
      (hcontpt w).tendsto.comp hwtend
    have h2 : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (v (φ n)))
        atTop (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ))) := by
      have htφ : Tendsto (fun n : ℕ => t (φ n)) atTop (𝓝 m) := htend.comp hφ.tendsto_atTop
      have hsm2 : Tendsto (fun n : ℕ => t (φ n) • ξ) atTop (𝓝 (m • ξ)) := htφ.smul_const ξ
      have h3 : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (t (φ n) • ξ))
          atTop (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet p (m • ξ))) :=
        (hcontpt (m • ξ)).tendsto.comp hsm2
      refine h3.congr' ?_
      filter_upwards with n
      exact (hvG (φ n)).symm
    exact tendsto_nhds_unique h1 h2
  by_cases hvw : w = m • ξ
  · -- the merging alternative: two distinct sequences with the same image through `m • ξ`
    right
    rintro ⟨s, hs, hinjs⟩
    have hsw : s ∈ 𝓝 w := by rw [hvw]; exact hs
    have h1 : ∀ᶠ n : ℕ in atTop, v (φ n) ∈ s := hwtend.eventually hsw
    have h2 : ∀ᶠ n : ℕ in atTop, t (φ n) • ξ ∈ s := by
      have h4 : Tendsto (fun n : ℕ => t (φ n) • ξ) atTop (𝓝 w) := by
        rw [hvw]
        have htφ : Tendsto (fun n : ℕ => t (φ n)) atTop (𝓝 m) := htend.comp hφ.tendsto_atTop
        exact htφ.smul_const ξ
      exact h4.eventually hsw
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    have heq : Submission.GlobalExp.GExp (cov := cov) hmet p (v (φ n))
        = Submission.GlobalExp.GExp (cov := cov) hmet p (t (φ n) • ξ) :=
      hvG (φ n)
    have heqn : v (φ n) = t (φ n) • ξ := hinjs _ hn1 _ hn2 heq
    have hnorm : ‖v (φ n)‖ = t (φ n) := by
      rw [heqn, norm_smul, Real.norm_of_nonneg (le_of_lt (lt_trans hm (htgt (φ n)))), hξ, mul_one]
    exact absurd hnorm (ne_of_lt (hvlt (φ n)))
  · exact Or.inl ⟨w, hvw, hw, hGw⟩

/-! ## 4. Reversing a minimising geodesic: the velocity at the far end -/

/-- **The reverse of a minimising geodesic.**  Suppose `U` lies in the tangential segment domain of
`q` (so the ray of `U` is strictly minimising at `‖U‖`), `p = GExp q U`, and `v` is a vector at `p`
of norm `‖U‖` with `GExp p v = q`.  Then `v` is the velocity at time `1` of the ray of `U`, with the
sign reversed: `v = -γ̇_U(1)`.

Classically: the geodesic from `p` with initial velocity `v` is minimising (it realises the distance
`‖v‖ = d(p,q)`), so its reversal is the unique minimising geodesic from `q` to `p`, i.e. the ray of
`U`. -/
theorem curveVelocity_ray_one_eq_neg
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {U : TangentSpace I q} (hU : U ≠ 0)
    (hseg : U ∈ Submission.SegmentDomain.segmentDomain hmet q)
    {p : M} (hUp : Submission.GlobalExp.GExp (cov := cov) hmet q U = p)
    {v : TangentSpace I p} (hvG : Submission.GlobalExp.GExp (cov := cov) hmet p v = q)
    (hvn : ‖v‖ = ‖U‖) :
    Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) 1 = -v := by
  classical
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvn
    linarith
  have hray_sm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hvne
  have hray_geo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hvne t
  have hray_ne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t ≠ 0 :=
    fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hvne t
  have hray_v : Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) 0 = v :=
    Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hvne
  have hray_norm : ∀ t : ℝ, t ≠ 0 → ‖Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t‖ = ‖v‖ :=
    fun t h => Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hvne h
  -- the reversed curve `s ↦ GExp p ((1 - s) • v)`
  have hrev_sm : ContMDiff 𝓘(ℝ) I ∞
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) :=
    hray_sm.comp (contMDiff_const.sub contMDiff_id)
  have hrev_geo : ∀ t ∈ Set.Ioo (-1 : ℝ) 3, Submission.Geodesic.IsGeodesicAt cov
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) t := by
    intro t ht
    have h1 : (-1 : ℝ) * t + 1 ∈ Set.Ioo (-3 : ℝ) 3 :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov)
      (σ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v))
      (c := -3) (d := 3) (a := -1) (b := 1) (by norm_num)
      (hray_sm.contMDiffOn.mono (Set.subset_univ _)) (fun y _ => hray_geo y) h1
    have h2 : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (((-1 : ℝ) * s + 1) • v))
        = (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) := by
      funext s
      rw [show (-1 : ℝ) * s + 1 = 1 - s from by ring]
    rw [h2] at h
    exact h
  have hrev_ne : ∀ t ∈ Set.Ioo (-1 : ℝ) 3, Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) t ≠ 0 := by
    intro t _
    rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) (t := 1) (r := t)
      ((hray_sm (1 - t)).mdifferentiableAt (by simp))]
    exact neg_ne_zero.mpr (hray_ne (1 - t))
  have hrev0 : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) 0 = q := by
    show Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - 0) • v) = q
    rw [sub_zero, one_smul]
    exact hvG
  have hrev1 : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) 1 = p := by
    show Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - 1) • v) = p
    rw [sub_self, zero_smul, Submission.GlobalExp.GExp_zero]
  set W : TangentSpace I q := Submission.Geodesic.curveVelocity (I := I)
    (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) 0 with hWdef
  have hWne : W ≠ 0 := by rw [hWdef]; exact hrev_ne 0 ⟨by norm_num, by norm_num⟩
  -- the reversed curve is the ray of `W` on `[0,2]`
  have hrayW : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) t
        = Submission.GlobalExp.GExp (cov := cov) hmet q (t • W) :=
    Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet (p := q) (V := W) hWne
      (a := -1) (b := 3) (T := 2) (by norm_num) (by norm_num) (by norm_num)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v))
      hrev_sm.contMDiffOn (fun t ht => hrev_geo t ht) (fun t ht => hrev_ne t ht) hrev0 hWdef.symm
  have hWp : Submission.GlobalExp.GExp (cov := cov) hmet q W = p := by
    have h := hrayW 1 (by norm_num)
    rw [hrev1, one_smul] at h
    exact h.symm
  have hWnorm : ‖W‖ = ‖U‖ := by
    have h2 : ‖W‖ = ‖Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) 1‖ := by
      rw [hWdef]
      rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I)
        (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) (t := 1) (r := 0)
        ((hray_sm (1 - 0)).mdifferentiableAt (by simp))]
      rw [show (1 : ℝ) - 0 = 1 from by ring]
      rw [one_smul, hvG]
      exact Submission.InjRadiusCut.norm_neg_tangent _
    rw [h2, hray_norm 1 (by norm_num), hvn]
  -- uniqueness of the minimising vector from `q` to `p`
  have hWU : W = U :=
    minimiser_unique_of_mem_segmentDomain (cov := cov) hmet htor hU hseg hUp hWp hWnorm
  -- the reversed curve agrees with the ray of `U` near `t = 1`
  have hev : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v))
      =ᶠ[𝓝 (1 : ℝ)] (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 by norm_num)]
      with t ht
    have h := hrayW t (Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩)
    rw [hWU] at h
    exact h
  have hvel : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((1 - s) • v)) 1
      = Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • U)) 1 :=
    Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev
  rw [← hvel]
  rw [Submission.HopfRinow.curveVelocity_comp_sub_neg_at (I := I)
    (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) (t := 1) (r := 1)
    ((hray_sm (1 - 1)).mdifferentiableAt (by simp))]
  rw [show (1 : ℝ) - 1 = 0 from by ring]
  rw [hray_v]


/-! ## 5. The main theorem -/

theorem segmentDomain_endpoint_revVelocity_aux
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ : M} {r m : ℝ} (hm : 0 < m) (hmr : m < r)
    (hinj : Submission.InjRadius.InjAtLeast hmet x₀ r)
    {ξ : TangentSpace I x₀} (hξ : ‖ξ‖ = 1) :
    m • (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)
      ∈ Submission.SegmentDomain.segmentDomain hmet
          (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ)) := by
  classical
  have hξne : ξ ≠ 0 := by intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hwn : ‖Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m‖ = 1 :=
    norm_curveVelocity_GExp_ray_eq_one (cov := cov) hmet hξ hm
  have hnegn : ‖(-Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)‖ = 1 := by
    rw [Submission.InjRadiusCut.norm_neg_tangent, hwn]
  have hVnorm : ‖m • (-Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)‖ = m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm, hnegn, mul_one]
  have hVpos : 0 < ‖m • (-Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)‖ := by
    rw [hVnorm]; exact hm
  have hVne : m • (-Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m) ≠ 0 :=
    norm_pos_iff.mp hVpos
  have hunit := unitOf_smul_neg_curveVelocity (cov := cov) hmet hξ hm hVne
  refine Submission.SegmentDomain.mem_segmentDomain_of_norm_lt hmet hVne ?_
  rw [hVnorm, hunit]
  -- the reversed ray reaches `x₀` at time `m`
  have hGx₀ : Submission.GlobalExp.GExp (cov := cov) hmet
      (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ))
      (m • (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)) = x₀ := by
    have h := Submission.GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet x₀ hξ hm
      (s := m) hm.le le_rfl
    rw [show m - m = (0 : ℝ) from by ring, zero_smul, Submission.GlobalExp.GExp_zero] at h
    exact h
  have hdyx : Manifold.riemannianEDist I x₀
      (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ)) = ENNReal.ofReal m :=
    Submission.CutTime.edist_GExp_smul_eq_of_injAtLeast (cov := cov) hmet htor (hinj := hinj)
      hξ hm.le hmr.le
  have hmin : m ∈ Submission.CutTime.minimisingSet (I := I) hmet
      (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ))
      (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m) := by
    refine ⟨hm.le, ?_⟩
    rw [hGx₀, Manifold.riemannianEDist_comm]
    exact hdyx
  have hle : m ≤ Submission.CutTime.cutTime (I := I) hmet
      (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ))
      (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m) :=
    ((Submission.CutTime.mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hnegn).mp hmin).2
  by_contra hcon
  have hcut : Submission.CutTime.cutTime (I := I) hmet
      (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ))
      (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m) = m :=
    le_antisymm (not_lt.mp hcon) hle
  rcases exists_two_minimising_or_not_locallyInjective_of_cutTime_noinj (cov := cov) hmet htor hnegn hm hcut with
    ⟨v, hveq_ne, hvn, hGv⟩ | hnotloc
  · -- case (i): a second minimising vector, killed by the reversal identity
    exfalso
    have hUne : m • ξ ≠ 0 := by
      intro h0
      have h : ‖m • ξ‖ = 0 := by rw [h0, norm_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm, hξ, mul_one] at h
      linarith
    have hUxnorm : ‖m • ξ‖ = m := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm, hξ, mul_one]
    have hunitξ : Submission.GlobalExp.unitOf (m • ξ) hUne = ξ := by
      rw [Submission.GlobalExp.unitOf, hUxnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hm), one_smul]
    have hcutξ : m < Submission.CutTime.cutTime (I := I) hmet x₀ ξ :=
      lt_of_lt_of_le hmr (Submission.CutTime.injAtLeast_le_cutTime (cov := cov) hmet htor hinj hξ)
    have hsegU : m • ξ ∈ Submission.SegmentDomain.segmentDomain hmet x₀ :=
      Submission.SegmentDomain.mem_segmentDomain_of_norm_lt hmet hUne
        (by rw [hUxnorm, hunitξ]; exact hcutξ)
    have hGv' : Submission.GlobalExp.GExp (cov := cov) hmet
        (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ)) v = x₀ := by
      rw [hGv]; exact hGx₀
    have hrev : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • (m • ξ))) 1 = -v :=
      curveVelocity_ray_one_eq_neg (cov := cov) hmet htor hUne hsegU rfl hGv'
        (by rw [hvn, hUxnorm])
    have hrescale : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • (m • ξ))) 1
        = m • Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m :=
      curveVelocity_ray_smul_one (cov := cov) hmet (x := x₀) (v := ξ) (a := m) hξne
    have hvfin : v = m • (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m) := by
      have h1 : -v = m • Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m := by
        rw [← hrev, hrescale]
      rw [smul_neg, ← h1, neg_neg]
    exact hveq_ne hvfin
  · -- case (ii): a conjugate time at `m` along the ray of `ξ`
    exfalso
    have hmf := Submission.GExpLocalInj.not_injective_mfderiv_of_not_locallyInjective
      (cov := cov) hmet hnotloc
    have hNotInv := Submission.GExpLocalInj.not_isInvertible_of_not_injective (cov := cov) hmet hmf
    have hconj := (Submission.SingularConj.singularImpConjTime_of_torsion_free (cov := cov) hmet htor)
      (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ)) hVne hNotInv
    rw [hunit, hVnorm] at hconj
    have hconj2 := isConjugateTime_comp_sub (cov := cov) hconj
    have hfun : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
          (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ))
          ((m - s) • (-Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)))
        = (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) := by
      funext s
      rw [GExp_neg_velocity_of_ray_all (cov := cov) hmet htor hξ hm (m - s),
        show m - (m - s) = s from by ring]
    rw [hfun] at hconj2
    have hle2 := Submission.ConjEnergy.cutTime_le_of_isConjugateTime (cov := cov) hmet htor hξ hconj2
    have hge := Submission.CutTime.injAtLeast_le_cutTime (cov := cov) hmet htor hinj hξ
    linarith


theorem segmentDomain_endpoint_revVelocity :
    Work.OddBound.polygon.RevVelocityInSegmentDomain := by
  intro E _ _ _ _ H _ I M _ _ _ _ _ _ _ _ _ _ _ cov _ hmet htor x₀ r m hm hmr hinj ξ hξ
  exact segmentDomain_endpoint_revVelocity_aux (cov := cov) hmet htor hm hmr hinj hξ

end Work.OddBound.polygon
