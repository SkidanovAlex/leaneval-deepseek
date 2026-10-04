import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.Lib
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.OddBound.sqDistChart.sqDist_contDiffAt_charts

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The fibre norm is smooth away from the origin.**  For a `C^∞` map `Φ` into a normed space
taking a non-zero value at `y`, the function `z ↦ ‖Φ z‖` is `C^∞` at `y`. -/
theorem eik_v2_norm_comp
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    {Φ : M → T} {y : M} (hΦ : ContMDiffAt I (𝓘(ℝ, T)) ∞ Φ y) (hne : Φ y ≠ 0) :
    CMDiffAt ∞ (fun z : M => ‖Φ z‖) y := by
  have h1 : ContMDiffAt (𝓘(ℝ, T)) (𝓘(ℝ, ℝ)) ∞ (fun w : T => ‖w‖) (Φ y) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_norm ℝ hne)
  exact h1.comp y hΦ

section GlobalInverse

variable [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **A smooth local inverse of the exponential map at a point with invertible differential.**
If the manifold derivative of `GExp p` at `w` is invertible, then there is `Φ : M → T_pM`, smooth at
`y = GExp p w`, with `Φ y = w` and `GExp p (Φ z) = z` for `z` near `y`. -/
theorem eik_v2_localInverse_GExp
    (hmet : IsMetricCompatible cov) (p : M) {y : M} {w : TangentSpace I p}
    (hw : Submission.GlobalExp.GExp (cov := cov) hmet p w = y)
    (hinv : (mfderiv 𝓘(ℝ, E) I (Submission.XuLift.gexpMap (cov := cov) hmet p)
      (show E from w)).IsInvertible) :
    ∃ Φ : M → TangentSpace I p,
      ContMDiffAt I (𝓘(ℝ, TangentSpace I p)) ∞ Φ y ∧
      Φ y = w ∧
      (∀ᶠ z in 𝓝 y, Submission.GlobalExp.GExp (cov := cov) hmet p (Φ z) = z) := by
  have hLD := Submission.XuLift.isLocalDiffeomorphAt_GExp (cov := cov) hmet p hinv
  have hbase : Submission.XuLift.gexpMap (cov := cov) hmet p (show E from w) = y := by
    rw [Submission.XuLift.gexpMap_apply]
    exact hw
  refine ⟨fun z => (show TangentSpace I p from ⇑hLD.localInverse z), ?_, ?_, ?_⟩
  · have h1 : ContMDiffAt I 𝓘(ℝ, E) ∞ (⇑hLD.localInverse)
        (Submission.XuLift.gexpMap (cov := cov) hmet p (show E from w)) :=
      hLD.localInverse_contMDiffAt
    rw [hbase] at h1
    exact (ContinuousLinearMap.contMDiff
        ((tangentSpaceCastModel I p).symm : E →L[ℝ] TangentSpace I p)).contMDiffAt.comp y h1
  · have h := hLD.localInverse_left_inv hLD.localInverse_mem_target
    change (show TangentSpace I p from ⇑hLD.localInverse y) = w
    rw [← hbase, h]
  · have hev := hLD.localInverse_eventuallyEq_right
    rw [hbase] at hev
    filter_upwards [hev] with z hz
    simpa only [Function.comp_apply, Submission.XuLift.gexpMap_apply, id_eq] using hz

end GlobalInverse

section DistEqNorm

variable [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **Below the injectivity radius the distance to `p` is the norm of the local inverse of the
exponential map.**  If `Φ` is a local right inverse of `GExp p` near `y` with `Φ y = v`,
`‖v‖ < ρ`, `rdist p y < ρ` and `InjAtLeast hmet p ρ`, then `rdist p z = ‖Φ z‖` near `y`. -/
theorem eik_v2_rdist_eq_norm
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p : M) {ρ : ℝ} (hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet p ρ)
    {v : TangentSpace I p} (hv : ‖v‖ < ρ)
    {y : M} (hrdy : rdist (I := I) p y < ρ)
    {Φ : M → TangentSpace I p} (hΦy : Φ y = v)
    (hΦG : ∀ᶠ z in 𝓝 y, Submission.GlobalExp.GExp (cov := cov) hmet p (Φ z) = z)
    (hΦc : ContinuousAt Φ y) :
    ∀ᶠ z in 𝓝 y, rdist (I := I) p z = ‖Φ z‖ := by
  have hcont : Continuous (fun z : M => rdist (I := I) p z) := rdist_continuous (I := I) p
  have h1 : ∀ᶠ z in 𝓝 y, rdist (I := I) p z < ρ :=
    hcont.continuousAt.eventually (isOpen_Iio.mem_nhds hrdy)
  have h2 : ∀ᶠ z in 𝓝 y, ‖Φ z‖ < ρ :=
    hΦc.norm.eventually (isOpen_Iio.mem_nhds (by simpa only [Set.mem_Iio, hΦy] using hv))
  filter_upwards [h1, h2, hΦG] with z hzρ hzΦ hzG
  obtain ⟨u, huG, hud⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p z
  have hu : ‖u‖ = rdist (I := I) p z := by
    rw [Work.Diff.C.rdist, hud, ENNReal.toReal_ofReal (norm_nonneg u)]
  have huρ : ‖u‖ < ρ := by rw [hu]; exact hzρ
  have heq : Φ z = u := hinj (Φ z) u hzΦ huρ (by rw [hzG, huG])
  rw [heq, ← hu]

end DistEqNorm

-- ROUTE.  `y` is strictly inside the injectivity radius `ρ` of `p` (`hy0`, `hy`), so `y` is not a
-- cut point of `p`, `GExp p` is a local diffeomorphism at the vector `v` with `GExp p v = y`, and
-- `rdist p ·` is smooth at `y` with `∇(rdist p ·)(y)` the unit radial vector.
-- Concretely: by Hopf–Rinow there is `v : T_pM` with `‖v‖ = rdist p y` and `GExp p v = y`
-- (`Submission.Work.Diff.C.ray_cover`, or `Submission.HopfRinow2`), and `InjAllAtLeast hmet ρ`
-- with `‖v‖ < ρ` makes `mfderiv (GExp p) v` invertible: the PROVED lemma
-- `Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt`
-- (`Submission/Work/OddBound/sqDistChart/sqDist_contDiffAt_charts.lean`) is exactly
-- "`InjAtLeast` + `‖w‖ < r` ⟹ mfderiv GExp w is invertible"; combine with the smooth local inverse
-- kit (`Submission.Work.Diff.C.GExp_localInverse`, `Submission.CutTime`, `Submission.InjRadiusCut`).
-- Then `rdist p z = ‖(GExp p)⁻¹ z‖` near `y` because the segment is minimising
-- (`Submission.Minimising`, `Work.Diff.C.ray_minimising`), so `rdist p ·` is smooth at `y` as a
-- composition of the smooth local inverse with the norm.
-- The gradient statement is Gauss' lemma / the eikonal equation: the differential of
-- `z ↦ ‖·‖` at `v` is `⟪v, ·⟫ / ‖v‖`, transferred through the inverse, and `‖v‖ = rdist p y`, so
-- `⟪∇d, ∇d⟫ = 1`.  PROVED helper to use: `Submission.Work.Diff.C.rgrad_rdist_eikonal`
-- (the eikonal equation from radial differentiability and the fact that the unit radial field has
-- `⟨∇d, ∇d⟩ = 1`), plus `Submission.Work.Diff.C.rgrad_fcos`.
-- `hy0` is needed: `rdist p ·` is not smooth at `p`.
theorem eikonal_of_inj_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hInj : Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) hmet ρ)
    (p : M) {y : M} (hy0 : 0 < rdist (I := I) p y) (hy : rdist (I := I) p y < ρ) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) y ∧
      Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) y)
        (rgrad (I := I) (rdist (I := I) p) y) = 1 := by
  classical
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  -- A minimising vector at `p` for `y` (Hopf–Rinow).
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p y
  have hnorm : ‖v‖ = rdist (I := I) p y := by
    rw [Work.Diff.C.rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  have hvρ : ‖v‖ < ρ := hnorm ▸ hy
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith
  -- The differential of `GExp p` at `v` is invertible (injectivity radius).
  have hinv : (mfderiv 𝓘(ℝ, E) I (Submission.XuLift.gexpMap (cov := cov) hmet p)
      (show E from v)).IsInvertible := by
    show (mfderiv 𝓘(ℝ, E) I (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet p u)
      (show E from v)).IsInvertible
    exact Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt (I := I) (cov := cov)
      hmet htor (hInj p) hvρ
  -- A smooth local inverse of `GExp p` near `y`.
  obtain ⟨Φ, hΦsm, hΦy, hΦG⟩ :=
    eik_v2_localInverse_GExp (I := I) (cov := cov) hmet p hvG hinv
  -- The distance is the norm of the local inverse near `y`.
  have hΦc : ContinuousAt Φ y := hΦsm.continuousAt
  have hev : ∀ᶠ z in 𝓝 y, rdist (I := I) p z = ‖Φ z‖ :=
    eik_v2_rdist_eq_norm (I := I) (cov := cov) hmet htor p (hInj p) hvρ hy hΦy hΦG hΦc
  have hne : Φ y ≠ 0 := by
    rw [hΦy]
    exact hvne
  -- Smoothness of `rdist p ·` at `y`.
  have hsm : CMDiffAt ∞ (fun z : M => rdist (I := I) p z) y :=
    (eik_v2_norm_comp (I := I) (Φ := Φ) hΦsm hne).congr_of_eventuallyEq hev
  refine ⟨hsm, ?_⟩
  exact rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor (ne_of_gt hy0) hsm

end Work.Diff.C
