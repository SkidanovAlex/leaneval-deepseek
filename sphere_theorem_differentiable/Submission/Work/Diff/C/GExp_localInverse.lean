import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.XuLift
import Submission.GExpLocalInj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: the local inverse of the exponential map at a point

The classical high-pinching sphere theorem is proved in area C through the function
`y ↦ cos (rdist q y)` and its Hessian.  The starting point is the existence of a *local inverse*
`Φ` of the exponential map `GExp q` at `q`, which is smooth near `q`, vanishes at `q`, has
differential the identity there, and — crucially for the distance computation — satisfies
`rdist q y = ‖Φ y‖` near `q`, the norm being the **fibre** (Riemannian) norm on `T_qM`.

This file proves that statement.

## Strategy

The statement lives in the tangent-space flavour (`Φ : M → TangentSpace I q`, smooth for the model
`𝓘(ℝ, TangentSpace I q)`).  The workspace's smoothness theory for the exponential map is stated in
the **model** flavour (`Submission.XuLift.gexpMap hmet q : E → M`), because `TangentSpace I q` is a
non-reducible type synonym of `E` carrying *different* `NormedAddCommGroup`/`NormedSpace` instances.
The two flavours are bridged by the canonical continuous linear equivalence

`eK := (tangentSpaceCastModel I q).symm : E ≃L[ℝ] TangentSpace I q`,

whose defining function is the identity (`eK u = u`, definitionally).  Concretely:

* `Submission.XuLift.isLocalDiffeomorphAt_GExp` (with `mfderiv_GExp_zero` for the invertibility of
  the differential at `0`) gives the model-flavour local diffeomorphism `hLD` of `gexpMap hmet q` at
  `0`, whose `localInverse` is `ΦE : M → E`;
* the required `Φ` is `fun y => eK (ΦE y)` (i.e. `ΦE` read in the tangent space);
* `Φ` is smooth near `q` because `eK` is a continuous linear map (hence `C^∞`, by
  `ContinuousLinearMap.contMDiff`) and `ΦE` is smooth on the source of `hLD.localInverse`;
* `Φ q = 0` since `ΦE q = 0` (base-point bookkeeping through `GExp_zero`);
* `mfderiv Φ q = id`: the chain rule (`mfderiv_comp`) applied to `Φ = eK ∘ ΦE` gives
  `mfderiv Φ q = (mfderiv eK _) ∘L (mfderiv ΦE _)`; the first factor is `eK`
  (`ContinuousLinearEquiv.hasMFDerivAt`), and the second is the identity because
  `mfderiv (gexpMap) 0 = id` and `(mfderivToContinuousLinearEquiv _).left_inv`;
* the last conjunct is the local minimality of `GExp` (`exists_pos_riemannianEDist_GExp_eq`)
  together with `sqrt_chartGram_self`, the fibre norm being `√(chartGram q q v v)`.
-/

set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C

theorem GExp_localInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (q : M) :
    ∃ Φ : M → TangentSpace I q,
      (∀ᶠ y in 𝓝 q, ContMDiffAt I (𝓘(ℝ, TangentSpace I q)) ∞ Φ y) ∧
      Φ q = 0 ∧
      mfderiv I (𝓘(ℝ, TangentSpace I q)) Φ q = ContinuousLinearMap.id ℝ (TangentSpace I q) ∧
      (∀ᶠ y in 𝓝 q, Submission.GlobalExp.GExp (cov := cov) hmet q (Φ y) = y ∧
        Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φ y‖) := by
  classical
  -- The differential of the model-space exponential map at `0` is the identity.
  have hzero : mfderiv 𝓘(ℝ, E) I (Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)
      = ContinuousLinearMap.id ℝ E := by
    show mfderiv 𝓘(ℝ, E) I
      (fun v : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from v))
      (0 : E) = ContinuousLinearMap.id ℝ E
    exact Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet q
  have hinv : (mfderiv 𝓘(ℝ, E) I (Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℝ E, by rw [hzero]; ext v; rfl⟩
  -- The model-flavour local diffeomorphism and its local inverse.
  have hLD : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E) :=
    Submission.XuLift.isLocalDiffeomorphAt_GExp (cov := cov) hmet q hinv
  set ΦE : M → E := ⇑hLD.localInverse.toPartialEquiv with hΦE
  -- The identity, read as a continuous linear equivalence `E ≃L[ℝ] T_qM`.
  let eK : E ≃L[ℝ] TangentSpace I q := (tangentSpaceCastModel I q).symm
  -- Bookkeeping of the base point: the local diffeomorphism lives at `gexpMap q 0 = q`.
  have hbase : (Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E) = q := by
    rw [Submission.XuLift.gexpMap_apply]
    show Submission.GlobalExp.GExp (cov := cov) hmet q (0 : TangentSpace I q) = q
    exact Submission.GlobalExp.GExp_zero hmet q
  have hsrc : hLD.localInverse.source ∈ 𝓝 q := by
    have h := hLD.localInverse_open_source.mem_nhds hLD.localInverse_mem_source
    rwa [hbase] at h
  have hΦE0 : ΦE q = 0 := by
    have h := hLD.localInverse_left_inv hLD.localInverse_mem_target
    rw [hbase] at h
    simpa [hΦE] using h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  -- The differential of the local inverse is the identity (its differential is inverse to
  -- `mfderiv (gexpMap) 0 = id`).
  have hmfΦE : mfderiv I 𝓘(ℝ, E) ΦE ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E))
      = ContinuousLinearMap.id ℝ E := by
    set e := hLD.mfderivToContinuousLinearEquiv hn with he
    have hcoe : (e : TangentSpace 𝓘(ℝ, E) (0:E) →L[ℝ]
          TangentSpace I ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)))
        = mfderiv% (Submission.XuLift.gexpMap (cov := cov) hmet q) (0:E) :=
      IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hLD hn
    have hinv_id : ∀ v : TangentSpace I ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)),
        e.invFun v = v := by
      intro v
      have h1 : e.invFun (e.toFun (show TangentSpace 𝓘(ℝ, E) (0:E) from v))
          = (show TangentSpace 𝓘(ℝ, E) (0:E) from v) :=
        e.left_inv (show TangentSpace 𝓘(ℝ, E) (0:E) from v)
      have h2 : e.toFun (show TangentSpace 𝓘(ℝ, E) (0:E) from v) = v := by
        change (mfderiv% (Submission.XuLift.gexpMap (cov := cov) hmet q) (0:E))
          (show TangentSpace 𝓘(ℝ, E) (0:E) from v) = v
        rw [hzero]
        rfl
      rw [h2] at h1
      exact h1
    ext v
    change e.invFun v = v
    exact hinv_id v
  refine ⟨fun y => eK (ΦE y), ?_, ?_, ?_, ?_⟩
  · -- Smoothness of `Φ = eK ∘ ΦE`.
    filter_upwards [hsrc] with y hy
    have hy' : ContMDiffAt I 𝓘(ℝ, E) ∞ ΦE y :=
      hLD.localInverse_contMDiffOn.contMDiffAt (hLD.localInverse_open_source.mem_nhds hy)
    exact (ContinuousLinearMap.contMDiff (eK : E →L[ℝ] TangentSpace I q)).contMDiffAt.comp y hy'
  · -- `Φ q = 0`.
    show eK (ΦE q) = 0
    rw [hΦE0]
    exact map_zero eK
  · -- The differential of `Φ` at `q` is the identity (chain rule).
    have hkdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace I q) (⇑eK)
        (ΦE ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E))) :=
      (ContinuousLinearMap.contMDiff (eK : E →L[ℝ] TangentSpace I q)).contMDiffAt.mdifferentiableAt hn
    have hΦEdiff : MDifferentiableAt I 𝓘(ℝ, E) ΦE
        ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)) :=
      hLD.localInverse_mdifferentiableAt hn
    have hchain : mfderiv I 𝓘(ℝ, TangentSpace I q) (fun y : M => eK (ΦE y))
        ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E))
        = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace I q) (⇑eK)
            (ΦE ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E))))
          ∘SL (mfderiv I 𝓘(ℝ, E) ΦE ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E))) :=
      mfderiv_comp ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)) hkdiff hΦEdiff
    have hκmf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace I q) (⇑eK)
        (ΦE ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)))
        = (eK : E →L[ℝ] TangentSpace I q) :=
      (ContinuousLinearEquiv.hasMFDerivAt eK
        (x := ΦE ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E)))).mfderiv
    have hres : mfderiv I 𝓘(ℝ, TangentSpace I q) (fun y : M => eK (ΦE y))
        ((Submission.XuLift.gexpMap (cov := cov) hmet q) (0 : E))
        = ContinuousLinearMap.id ℝ (TangentSpace I q) := by
      rw [hchain, hκmf, hmfΦE]
      ext v
      rfl
    have hres' : mfderiv I 𝓘(ℝ, TangentSpace I q) (fun y : M => eK (ΦE y)) q
        = ContinuousLinearMap.id ℝ (TangentSpace I q) := by
      rw [← hbase]
      exact hres
    exact hres'
  · -- `GExp q (Φ y) = y` and `rdist q y = ‖Φ y‖` near `q`.
    obtain ⟨ρ₂, hρ₂, hρ₂eq⟩ :=
      Submission.GlobalExp.exists_pos_riemannianEDist_GExp_eq (cov := cov) hmet htor q
    have hev1 : (fun y => Submission.GlobalExp.GExp (cov := cov) hmet q (eK (ΦE y)))
        =ᶠ[𝓝 q] id := by
      have h := hLD.localInverse_eventuallyEq_right
      rw [hbase] at h
      filter_upwards [h] with y hy
      simp only [Function.comp_apply] at hy
      rw [show (id y : M) = y from rfl] at hy
      rw [show eK (ΦE y) = ΦE y from rfl]
      exact hy
    have hΦ_cont : ContinuousAt (fun y : M => eK (ΦE y)) q := by
      have h1 : ContinuousAt ΦE q := by
        have h := hLD.continuousAt_localInverse
        rwa [hbase] at h
      exact ((eK : E →L[ℝ] TangentSpace I q).continuous.continuousAt).comp h1
    have htend : Filter.Tendsto (fun y : M => eK (ΦE y)) (𝓝 q) (𝓝 (0 : TangentSpace I q)) := by
      rw [show (0 : TangentSpace I q) = eK (ΦE q) from by rw [hΦE0, map_zero]]
      exact hΦ_cont
    have hsmall : ∀ᶠ y in 𝓝 q, ‖eK (ΦE y)‖ < ρ₂ := by
      have hb : ∀ᶠ y in 𝓝 q, eK (ΦE y) ∈ Metric.ball (0 : TangentSpace I q) ρ₂ :=
        htend (Metric.ball_mem_nhds 0 hρ₂)
      filter_upwards [hb] with y hy
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      exact hy
    filter_upwards [hev1, hsmall] with y hy1 hy2
    constructor
    · exact hy1
    · show Work.Diff.C.rdist (I := I) (M := M) q y = ‖eK (ΦE y)‖
      have hy1' : Work.Diff.C.rdist (I := I) (M := M) q y
          = Work.Diff.C.rdist (I := I) (M := M) q
              (Submission.GlobalExp.GExp (cov := cov) hmet q (eK (ΦE y))) :=
        congrArg (fun z => Work.Diff.C.rdist (I := I) (M := M) q z) (by rw [hy1]; rfl)
      rw [hy1']
      show (Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (eK (ΦE y)))).toReal = ‖eK (ΦE y)‖
      rw [hρ₂eq (eK (ΦE y)) hy2]
      rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
      exact Submission.GlobalExp.sqrt_chartGram_self (I := I) (x := q) (eK (ΦE y))

end Work.Diff.C
