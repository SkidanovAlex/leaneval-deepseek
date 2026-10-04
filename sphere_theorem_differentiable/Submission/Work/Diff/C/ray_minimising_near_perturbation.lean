import Mathlib
import Submission.Work.Diff.C.HessLowerKit
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.EvenBound.FarthestPoint.edist_GExp_eq_norm_of_injAtLeast
import Submission.RayConj
import Submission.GExpSmooth
import Submission.GExpVelocity
import Submission.BrokenLength
import Submission.GExpRayZero

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative
open Submission.Geodesic
open Filter

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **A minimising ray is minimising up to its endpoint.**  If `u ≠ 0` and the ray of `u` from `p`
is minimising at time `1` (`d (p, GExp p u) = ‖u‖`), then for every `s ∈ [0,1]` the point
`GExp p (s • u)` is at distance `s * ‖u‖` from `p`. -/
theorem rdist_GExp_smul_of_minimising
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} {u : TangentSpace I p} (hu0 : u ≠ 0)
    (hmin : Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p u)
      = ENNReal.ofReal ‖u‖)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      = s * ‖u‖ := by
  have hun : ‖Submission.GlobalExp.unitOf u hu0‖ = 1 :=
    Submission.GlobalExp.unitOf_norm u hu0
  have hsc : ‖u‖ • Submission.GlobalExp.unitOf u hu0 = u := by
    rw [Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu0), one_smul]
  have hmin' : Manifold.riemannianEDist I p
      (Submission.GlobalExp.GExp (cov := cov) hmet p
        (‖u‖ • Submission.GlobalExp.unitOf u hu0)) = ENNReal.ofReal ‖u‖ := by
    rw [hsc]; exact hmin
  have hmul : (s * ‖u‖) • Submission.GlobalExp.unitOf u hu0 = s • u := by
    rw [mul_smul, hsc]
  have hkey := Submission.CutTime.edist_GExp_smul_eq_of_le_of_eq (I := I) (cov := cov) hmet hun
    (s := s * ‖u‖) (t := ‖u‖) (mul_nonneg hs0 (norm_nonneg u))
    (by nlinarith [norm_nonneg u]) hmin'
  rw [Work.Diff.C.rdist, ← hmul, hkey,
    ENNReal.toReal_ofReal (mul_nonneg hs0 (norm_nonneg u))]

/-- **The velocity at the endpoint of a minimising ray.**  For a minimising vector `u ≠ 0`, if the
distance function `rdist p ·` is smooth at the endpoint `GExp p u = GExp p (1 • u)` of the ray and
its gradient there is a unit vector, then the velocity at time `1` of the ray `s ↦ GExp p (s • u)`
is `‖u‖ • ∇(rdist p ·)`: the ray arrives with the (unique) unit gradient direction, scaled by its
speed. -/
theorem curveVelocity_GExp_eq_smul_rgrad
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} {u : TangentSpace I p} (hu0 : u ≠ 0)
    (hmin : Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p u)
      = ENNReal.ofReal ‖u‖)
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)))
    (hunit : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u))) = 1) :
    curveVelocity (I := I) (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1
      = ‖u‖ • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)) := by
  classical
  have hH : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
        = s * ‖u‖ :=
    fun s hs => rdist_GExp_smul_of_minimising (I := I) (M := M) (cov := cov) hmet hu0 hmin
      hs.1 hs.2
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hu0
  have hγmd : MDifferentiableAt 𝓘(ℝ) I
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1 :=
    (hγsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by decide)
  have hFmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)) :=
    hsm.mdifferentiableAt (by decide)
  have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℝ)
      (((fun z : M ↦ rdist (I := I) (M := M) p z) ∘
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)))) 1 :=
    hFmd.comp 1 hγmd
  have hderiv : deriv (fun s : ℝ ↦ rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))) 1 = ‖u‖ := by
    have h1 : HasDerivWithinAt (fun s : ℝ ↦ rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))) ‖u‖ (Set.Iic 1) 1 := by
      have hbase : HasDerivWithinAt (fun s : ℝ ↦ s * ‖u‖) ‖u‖ (Set.Iic 1) 1 := by
        simpa using (hasDerivWithinAt_id (1 : ℝ) (Set.Iic 1)).mul_const ‖u‖
      refine hbase.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin,
          (nhdsWithin_le_nhds (Ioi_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num)))]
          with t hts ht
        exact hH t ⟨le_of_lt (lt_trans (by norm_num) ht), hts⟩
      · exact hH 1 ⟨zero_le_one, le_rfl⟩
    have h2 : HasDerivWithinAt (fun s : ℝ ↦ rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)))
        (deriv (fun s : ℝ ↦ rdist (I := I) (M := M) p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))) 1) (Set.Iic 1) 1 :=
      hcomp.differentiableAt.hasDerivAt.hasDerivWithinAt
    have e1 := h1.derivWithin (uniqueDiffWithinAt_Iic 1)
    have e2 := h2.derivWithin (uniqueDiffWithinAt_Iic 1)
    rw [← e2]; exact e1
  have hchain : deriv (fun s : ℝ ↦ rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))) 1
      = mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u))
          (curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1) := by
    have h0 := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun z : M ↦ rdist (I := I) (M := M) p z)
      (γ := fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t := 1)
      hFmd hγmd
    rw [Submission.Geodesic.curveVelocity_apply]
    exact h0.symm
  have hinner : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)))
      (curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1) = ‖u‖ := by
    rw [Work.Diff.C.inner_rgrad]
    change mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u))
      (curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1) = ‖u‖
    rw [← hchain]
    exact hderiv
  have hsp : ‖curveVelocity (I := I)
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1‖ = ‖u‖ := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm]
    exact Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hu0 1
  have hunit' : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u))‖ = 1 := by
    have h := hunit
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)))]
  have hcs : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u)))
      (curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1)
      = ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u))‖
        * ‖curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1‖ := by
    rw [hunit', hsp, one_mul]
    exact hinner
  have hmul := inner_eq_norm_mul_iff.mp hcs
  rw [hsp, hunit'] at hmul
  have hmul' : (‖u‖ : ℝ) • rgrad (I := I) (M := M)
        (fun z : M ↦ rdist (I := I) (M := M) p z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • u))
      = curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) 1 := by
    simpa using hmul
  exact hmul'.symm

end Helpers


theorem ray_minimising_near_perturbation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (p : M) {v : TangentSpace I p} (hv0 : v ≠ 0)
    (hvK : ‖v‖ < Real.pi / Real.sqrt K)
    (hminv : Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p v)
      = ENNReal.ofReal ‖v‖)
    (hsm : CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p v))
    (hunit : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p v))
        (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p v)) = 1) :
    ∀ w : TangentSpace I p, ∀ᶠ s in 𝓝 (0 : ℝ),
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (v + s • w))
        = ENNReal.ofReal ‖v + s • w‖ := by
  classical
  set q : M := Submission.GlobalExp.GExp (cov := cov) hmet p v with hqdef
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hrdq : rdist (I := I) (M := M) p q = ‖v‖ := by
    rw [Work.Diff.C.rdist, hqdef, hminv, ENNReal.toReal_ofReal (norm_nonneg v)]
  obtain ⟨s₀, hs₀, hinj₀⟩ := Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
    (cov := cov) hmet htor hcurv hK hv0 hvK
  obtain ⟨δ₀, hδ₀pos, hball₀⟩ := Metric.mem_nhds_iff.mp hs₀
  have hinj_ball : ∀ a b : TangentSpace I p, ‖a - v‖ < δ₀ → ‖b - v‖ < δ₀ →
      Submission.GlobalExp.GExp (cov := cov) hmet p a
        = Submission.GlobalExp.GExp (cov := cov) hmet p b → a = b := by
    intro a b ha hb hab
    refine hinj₀ a (hball₀ ?_) b (hball₀ ?_) hab
    · rwa [Metric.mem_ball, dist_eq_norm]
    · rwa [Metric.mem_ball, dist_eq_norm]
  have key : ∃ δ : ℝ, 0 < δ ∧ ∀ u : TangentSpace I p, ‖u - v‖ < δ →
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p u)
        = ENNReal.ofReal ‖u‖ := by
    by_contra hcon
    push_neg at hcon
    choose u hu using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
    have hutend : Tendsto u atTop (𝓝 v) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have h1 : ∀ n : ℕ, dist (u n) v ≤ 1 / ((n : ℝ) + 1) := by
        intro n
        rw [dist_eq_norm]
        exact le_of_lt (hu n).1
      exact squeeze_zero (fun n => dist_nonneg) h1 tendsto_one_div_add_atTop_nhds_zero_nat
    have hex : ∀ n : ℕ, ∃ w : TangentSpace I p,
        Submission.GlobalExp.GExp (cov := cov) hmet p w
          = Submission.GlobalExp.GExp (cov := cov) hmet p (u n) ∧
        Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (u n))
          = ENNReal.ofReal ‖w‖ := by
      intro n
      exact Work.EvenBound.FarthestPoint.exists_geodesic_riemannianEDist_eq_of_lt_top
        (cov := cov) hmet htor p (Submission.GlobalExp.GExp (cov := cov) hmet p (u n))
        (lt_of_le_of_lt (Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet (u n))
          ENNReal.ofReal_lt_top)
    choose w hw using hex
    have hltn : ∀ n : ℕ, ‖w n‖ < ‖u n‖ := by
      intro n
      have h1 : ENNReal.ofReal ‖w n‖ < ENNReal.ofReal ‖u n‖ := by
        rw [← (hw n).2]
        exact lt_of_le_of_ne
          (Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet (u n)) (hu n).2
      exact ((ENNReal.ofReal_lt_ofReal_iff').mp h1).1
    have hrw : ∀ n : ℕ, rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (u n)) = ‖w n‖ := by
      intro n
      rw [Work.Diff.C.rdist, (hw n).2, ENNReal.toReal_ofReal (norm_nonneg (w n))]
    have hGtend : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (u n))
        atTop (𝓝 q) := by
      have hc : ContinuousAt (fun z : E => Submission.GlobalExp.GExp (cov := cov) hmet p
          (show TangentSpace I p from z)) (show E from v) :=
        (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p v).continuousAt
      have h' := hc.tendsto.comp hutend
      rw [hqdef]
      exact h'
    have hrdtend : Tendsto (fun n : ℕ => rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (u n))) atTop (𝓝 ‖v‖) := by
      have hcont : Continuous (fun z : M => rdist (I := I) (M := M) p z) :=
        Work.Diff.C.rdist_continuous (I := I) (M := M) p
      have h1 := hcont.continuousAt.tendsto.comp hGtend
      rw [hrdq] at h1
      exact h1
    have hwtend : Tendsto (fun n : ℕ => ‖w n‖) atTop (𝓝 ‖v‖) :=
      hrdtend.congr' (Eventually.of_forall fun n => (hrw n))
    have hbound : ∀ n : ℕ, w n ∈ Metric.closedBall (0 : TangentSpace I p) (‖v‖ + 1) := by
      intro n
      rw [Metric.mem_closedBall, dist_zero_right]
      refine le_of_lt (lt_of_lt_of_le (hltn n) ?_)
      calc ‖u n‖ = ‖(u n - v) + v‖ := by rw [sub_add_cancel]
        _ ≤ ‖u n - v‖ + ‖v‖ := norm_add_le _ _
        _ ≤ 1 / ((n : ℝ) + 1) + ‖v‖ := by
            have h1 : ‖u n - v‖ < 1 / ((n : ℝ) + 1) := (hu n).1
            have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith
        _ ≤ 1 + ‖v‖ := by
            have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith [Nat.cast_nonneg (α := ℝ) n]
            linarith
        _ = ‖v‖ + 1 := by ring
    haveI hproper : ProperSpace (TangentSpace I p) := by
      haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
      exact FiniteDimensional.proper ℝ (TangentSpace I p)
    obtain ⟨wstar, -, φ, hφ, hwtendφ⟩ :=
      (isCompact_closedBall (0 : TangentSpace I p) (‖v‖ + 1)).tendsto_subseq hbound
    have hwnorm : ‖wstar‖ = ‖v‖ := by
      have h1 : Tendsto (fun n : ℕ => ‖w (φ n)‖) atTop (𝓝 ‖wstar‖) := hwtendφ.norm
      have h2 : Tendsto (fun n : ℕ => ‖w (φ n)‖) atTop (𝓝 ‖v‖) :=
        hwtend.comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have hGw : Submission.GlobalExp.GExp (cov := cov) hmet p wstar = q := by
      have hc : ContinuousAt (fun z : E => Submission.GlobalExp.GExp (cov := cov) hmet p
          (show TangentSpace I p from z)) (show E from wstar) :=
        (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p wstar).continuousAt
      have h1 : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (w (φ n)))
          atTop (𝓝 (Submission.GlobalExp.GExp (cov := cov) hmet p wstar)) :=
        hc.tendsto.comp hwtendφ
      have h2 : Tendsto (fun n : ℕ => Submission.GlobalExp.GExp (cov := cov) hmet p (w (φ n)))
          atTop (𝓝 q) :=
        (hGtend.comp hφ.tendsto_atTop).congr'
          (Eventually.of_forall fun n => (hw (φ n)).1.symm)
      exact tendsto_nhds_unique h1 h2
    by_cases hwv : wstar = v
    · have hcloseu : ∀ᶠ n : ℕ in atTop, ‖u (φ n) - v‖ < δ₀ := by
        have h : Tendsto (fun n : ℕ => u (φ n)) atTop (𝓝 v) := hutend.comp hφ.tendsto_atTop
        exact (h.eventually (Metric.ball_mem_nhds v hδ₀pos)).mono (fun n hn => by
          simpa [Metric.mem_ball, dist_eq_norm] using hn)
      have hclosew : ∀ᶠ n : ℕ in atTop, ‖w (φ n) - v‖ < δ₀ := by
        have h : Tendsto (fun n : ℕ => w (φ n)) atTop (𝓝 v) := by
          rw [← hwv]; exact hwtendφ
        exact (h.eventually (Metric.ball_mem_nhds v hδ₀pos)).mono (fun n hn => by
          simpa [Metric.mem_ball, dist_eq_norm] using hn)
      obtain ⟨n, hn1, hn2⟩ := (hcloseu.and hclosew).exists
      have heq : w (φ n) = u (φ n) := hinj_ball _ _ hn2 hn1 (hw (φ n)).1
      have hlt := hltn (φ n)
      rw [heq] at hlt
      exact absurd hlt (lt_irrefl _)
    · have hw0 : wstar ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hwnorm
        exact absurd hwnorm.symm (ne_of_gt hvnorm_pos)
      have hminw : Manifold.riemannianEDist I p
          (Submission.GlobalExp.GExp (cov := cov) hmet p wstar)
          = ENNReal.ofReal ‖wstar‖ := by
        rw [hGw, hwnorm]
        exact hminv
      have hpt_v : Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • v) = q := by
        rw [one_smul, hqdef]
      have hpt_w : Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • wstar) = q := by
        rw [one_smul, hGw]
      have hsm_v : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • v)) := by
        rw [hpt_v]; exact hsm
      have hunit_v : Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • v)))
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • v))) = 1 := by
        rw [hpt_v]; exact hunit
      have hsm_w : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • wstar)) := by
        rw [hpt_w]; exact hsm
      have hunit_w : Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • wstar)))
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p ((1 : ℝ) • wstar))) = 1 := by
        rw [hpt_w]; exact hunit
      have hvel_v : curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) 1
          = ‖v‖ • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z) q := by
        have h0 := curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet hv0
          hminv hsm_v hunit_v
        rw [hpt_v] at h0
        exact h0
      have hvel_w : curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • wstar)) 1
          = ‖wstar‖ • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) p z) q := by
        have h0 := curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet hw0
          hminw hsm_w hunit_w
        rw [hpt_w] at h0
        exact h0
      have hveleq : curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) 1
          = curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • wstar)) 1 := by
        rw [hvel_v, hvel_w, hwnorm]
      have hEqOn : Set.EqOn (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • v))
          (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • wstar))
          (Set.Ioo (-1) 2) := by
        refine Submission.GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq (I := I) (cov := cov)
          (a := (-1 : ℝ)) (b := 2) ?_ ?_ ?_ ?_ ?_ ?_ ⟨by norm_num, by norm_num⟩ ?_ hveleq
        · exact (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hv0).mono
            (Set.subset_univ _)
        · exact (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hw0).mono
            (Set.subset_univ _)
        · intro t ht
          exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hv0 t
        · intro t ht
          exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hw0 t
        · intro t ht hzero
          have h := Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hv0 t
          rw [Submission.GeodesicSpeed.curveSpeed_eq_norm] at h
          rw [hzero, norm_zero] at h
          exact hvnorm_pos.ne' h.symm
        · intro t ht hzero
          have h := Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hw0 t
          rw [Submission.GeodesicSpeed.curveSpeed_eq_norm] at h
          rw [hzero, norm_zero] at h
          exact (ne_of_gt (by rw [hwnorm]; exact hvnorm_pos)) h.symm
        · rw [one_smul, one_smul, hGw, hqdef]
      have hev : (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • v))
          =ᶠ[𝓝 (0 : ℝ)]
          (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • wstar)) := by
        filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 2 by norm_num)] with t ht
        exact hEqOn ht
      have hvel0 : curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) 0
          = curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (s • wstar)) 0 :=
        Submission.RayJacobi.curveVelocity_congr (I := I) hev
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hv0,
        Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hw0] at hvel0
      exact hwv hvel0.symm
  obtain ⟨δ, hδpos, hkey⟩ := key
  intro w
  by_cases hw0 : w = 0
  · refine Filter.Eventually.of_forall (fun s : ℝ => ?_)
    rw [hw0, smul_zero, add_zero, ← hqdef]
    exact hminv
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    set ε : ℝ := min δ ‖v‖ / (1 + ‖w‖) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      exact div_pos (lt_min hδpos hvnorm_pos) (by positivity)
    have hεδ : ε * (1 + ‖w‖) ≤ δ := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ‖w‖)]
      exact mul_le_mul_of_nonneg_right (min_le_left δ ‖v‖) (by positivity)
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) hεpos) ?_
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    refine hkey (v + s • w) ?_
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖w‖ < ε * ‖w‖ := mul_lt_mul_of_pos_right hs hwpos
      _ ≤ ε * (1 + ‖w‖) := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) (le_of_lt hεpos)
      _ ≤ δ := hεδ

end Work.Diff.C
