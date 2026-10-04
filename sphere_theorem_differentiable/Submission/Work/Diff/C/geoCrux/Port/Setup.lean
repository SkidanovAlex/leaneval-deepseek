import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.Defs
import Submission.Work.Diff.C.geoCrux.RadialBase
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.Work.Diff.C.geoCrux.shape_polarized
import Submission.Work.Diff.C.geoCrux.rdist_min
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.JacobiLogDeriv
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.rgrad_fcos
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.Work.OddBound.sqDistChart.sqDist_contDiffAt_charts
import Submission.Work.OddBound.polygon.isConjugateTime_comp_sub
import Submission.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.OddBound.pvCrux.edist_GExp_ray_sub
import Submission.GExpTranslate
import Submission.RayJacobi
import Submission.CurvatureSym
import Submission.CutTime
import Submission.GExpRay2

set_option backward.isDefEq.respectTransparency.types false

/-!
# Setup for the two-centre core

Vocabulary and the elementary geodesic facts used by the proof of
`Work.Diff.C.geoCrux.Port.TwoCentreCoreProp` (`Submission/Work/Diff/C/geoCrux/twoCentre_core.lean`).

The geometric situation: a complete Riemannian manifold with a smooth metric-compatible torsion-free
connection, a point `q`, a unit vector `v ∈ T_qM` and the unit-speed geodesic
`gam s = GExp q (s • v)`.  The hypotheses `hHess`/`hgrad`/`hsmC` say that the metric is the round unit
sphere up to `ε₁`, and `hcut` says that every point has injectivity radius at least
`rho0 = π - arccos (1-c)`; in particular every ray is minimising up to `rho0` and there are no
conjugate points below `rho0`.

The two families of Jacobi fields along `gam`:

* `tcFwd ξ` — the forward variation field of the family of rays out of `q`
  (`tcFwd ξ s = ∂_r GExp q (s • (v + r ξ))|_0`, so `tcFwd ξ 0 = 0`, `∇tcFwd ξ (0) = ξ`);
* `tcBwd τ w η` — the backward variation field of the family of rays out of the point
  `p = gam τ` in the reversed direction `w = -γ'(τ)`
  (`tcBwd τ w η s = ∂_r GExp p ((τ-s) • (w + r η))|_0`, so `tcBwd η τ = 0`).

It is convenient to regard `tcBwd` as a field *along `gam`* — its value at parameter `s` lives at the
point `GExp p ((τ-s)•w)`, which is propositionally equal to `gam s` (the reversal identity
`GExp p ((τ-s)•w) = gam s` is `Submission.GExpTranslate.GExp_translate`).  Since
`TangentSpace I x` is definitionally `E`, the type ascription is legitimate; all *pairings* below are
taken with the metric at `gam s` (the true point).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux.Port

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## The geodesic ray -/

/-- The geodesic ray from `q` in the direction `v`. -/
noncomputable def tcGam (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) : ℝ → M :=
  fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)

/-- Its velocity. -/
noncomputable def tcVel (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (s : ℝ) :
    TangentSpace I (tcGam hmet q v s) :=
  Submission.Geodesic.curveVelocity (I := I) (tcGam hmet q v) s

/-- The forward variation field of the family of rays out of `q`. -/
noncomputable def tcFwd (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) :
    (s : ℝ) → TangentSpace I (tcGam hmet q v s) :=
  fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (v + r • ξ))) 0

/-- The backward variation field of the family of rays out of `p = gam τ`, in the reversed
direction `w = -γ'(τ)`: `tcBwd T w η s = ∂_r GExp p ((T-s) • (w + r η))|_0`.

Its type is that of a field along `gam` (the value lives at the point `GExp p ((T-s)•w) = gam s`). -/
noncomputable def tcBwd (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q)
    (T : ℝ) (w η : TangentSpace I (tcGam hmet q v T)) (s : ℝ) :
    TangentSpace I (tcGam hmet q v s) :=
  Submission.Geodesic.curveVelocity (I := I)
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
      (tcGam hmet q v T) ((T - s) • (w + r • η))) 0

/-! ## The basic facts about the ray -/

lemma tcVel_zero (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (hv0 : v ≠ 0) :
    tcVel (cov := cov) hmet q v 0 = v :=
  Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hv0

lemma tcVel_ne_zero (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (hv0 : v ≠ 0)
    (s : ℝ) : tcVel (cov := cov) hmet q v s ≠ 0 :=
  Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hv0 s

lemma tcVel_norm (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (hv0 : v ≠ 0)
    (s : ℝ) : ‖tcVel (cov := cov) hmet q v s‖ = ‖v‖ := by
  have h := Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet q hv0 s
  rw [Submission.GeodesicSpeed.curveSpeed_eq_norm] at h
  exact h

lemma tcGam_contMDiff (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q}
    (hv0 : v ≠ 0) : ContMDiff 𝓘(ℝ) I ∞ (tcGam (cov := cov) hmet q v) :=
  contMDiffOn_univ.mp (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hv0)

lemma tcGam_isGeodesicAt (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q}
    (hv0 : v ≠ 0) (s : ℝ) : Submission.Geodesic.IsGeodesicAt cov (tcGam (cov := cov) hmet q v) s :=
  Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hv0 s

/-! ## The reversal identity

The reversed ray out of `p = gam T` in the direction `-γ'(T)` retraces `gam`. -/

lemma tc_rev_point (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1)
    (T s : ℝ) :
    Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v T)
        ((T - s) • (-(tcVel (cov := cov) hmet q v T))) = tcGam (cov := cov) hmet q v s := by
  have h := Submission.GExpTranslate.GExp_translate (I := I) (M := M) (cov := cov) hmet q hvn T
    (-(T - s))
  have h2 : T + (-(T - s)) = s := by ring
  rw [h2] at h
  have h3 : (-(T - s)) • (Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (r • v)) T)
      = (T - s) • (-(Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (r • v)) T)) := by
    simp only [neg_smul, smul_neg]
  rw [h3] at h
  exact h

/-- The velocity of the reversed ray: at parameter `T - s` it is `-γ'(s)`. -/
lemma tc_rev_vel (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1)
    (hv0 : v ≠ 0) (T s : ℝ) :
    Submission.Geodesic.curveVelocity (I := I)
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v T)
        (t • (-(tcVel (cov := cov) hmet q v T)))) (T - s)
      = -(tcVel (cov := cov) hmet q v s) := by
  have hfun : (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
        (tcGam (cov := cov) hmet q v T) (t • (-(tcVel (cov := cov) hmet q v T))))
      = (fun t : ℝ => tcGam (cov := cov) hmet q v ((-1) * t + T)) := by
    funext t
    have h := tc_rev_point (cov := cov) hmet hvn T (T - t)
    have h3 : T - (T - t) = t := by ring
    rw [h3] at h
    have h4 : T - t = (-1) * t + T := by ring
    rw [h4] at h
    exact h
  rw [hfun]
  have hd : MDifferentiableAt 𝓘(ℝ) I (tcGam (cov := cov) hmet q v) ((-1) * (T - s) + T) :=
    ((tcGam_contMDiff (cov := cov) hmet hv0).contMDiffAt).mdifferentiableAt (by decide)
  rw [Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := tcGam (cov := cov) hmet q v)
    (c := -1) (d := T) (t := T - s) hd]
  have harg : (-1) * (T - s) + T = s := by ring
  rw [harg, neg_one_smul, smul_neg]
  rfl

/-! ## The distance functions along the ray -/

/-- `rdist q (gam t) = t` for `0 < t ≤ rho0`. -/
lemma tc_rdist_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ rho0 c) :
    rdist (I := I) (M := M) q (tcGam (cov := cov) hmet q v t) = t := by
  haveI : RegularSpace M := inferInstance
  have hnt : ‖(t • v : TangentSpace I q)‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le, hvn, mul_one]
  have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov)
    hmet htor (hcut q) (w := t • v) (by rw [hnt]; exact ht)
  rw [hnt] at h
  rw [Work.Diff.C.rdist]
  change (Manifold.riemannianEDist I q
    (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))).toReal = t
  rw [h, ENNReal.toReal_ofReal ht0.le]

/-- `rdist (gam T) (gam s) = T - s` for `s < T ≤ rho0`. -/
lemma tc_rdist_bwd (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {T : ℝ} (hT : T ≤ rho0 c) (hT0 : 0 < T)
    {s : ℝ} (hs : 0 ≤ s) (hsT : s < T) :
    rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v T) (tcGam (cov := cov) hmet q v s)
      = T - s := by
  haveI : RegularSpace M := inferInstance
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvn
    norm_num at hvn
  have hwn : ‖-(tcVel (cov := cov) hmet q v T)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 T, hvn]
  have hpos : 0 < T - s := sub_pos.mpr hsT
  have hle : T - s ≤ rho0 c := by linarith
  have hnt : ‖((T - s) • (-(tcVel (cov := cov) hmet q v T)) :
      TangentSpace I (tcGam (cov := cov) hmet q v T))‖ = T - s := by
    rw [norm_smul, Real.norm_of_nonneg hpos.le, hwn, mul_one]
  have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov)
    hmet htor (hcut (tcGam (cov := cov) hmet q v T))
    (w := (T - s) • (-(tcVel (cov := cov) hmet q v T))) (by rw [hnt]; exact hle)
  rw [hnt] at h
  have hpt := tc_rev_point (cov := cov) hmet hvn T s
  rw [← hpt]
  rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal hpos.le]

/-! ## Smoothness of the distance functions, from `hsmC` -/

/-- The distance function `rdist q` is `C^∞` at every point `y` with `0 < rdist q y ≤ rho0 c` at
which `fcos q` is smooth (`hsmC`).  This is
`Work.Diff.C.GeoCrux.rdist_smooth_of_le_rho` with the (unused) global diameter hypothesis removed. -/
lemma csm_rdist_of_le_rho {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q y : M} (hy0 : 0 < rdist (I := I) (M := M) q y)
    (hle : rdist (I := I) (M := M) q y ≤ rho0 c) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) y := by
  have hρπ : rho0 c ≤ Real.pi := by
    have h : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg (1 - c)
    rw [rho0]; linarith
  have hρlt : rho0 c < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    rw [rho0]; linarith
  have hcosρ : Real.cos (rho0 c) = -1 + c := by
    rw [rho0, Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hfcos_ge : -1 + c ≤ fcos (I := I) (M := M) q y := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := rdist (I := I) (M := M) q y) (y := rho0 c) hy0.le hρπ hle
    rw [hcosρ] at h
    exact h
  have hsm : CMDiffAt ∞ (fcos (I := I) (M := M) q) y := hsmC q y hfcos_ge
  have hdpi : rdist (I := I) (M := M) q y < Real.pi := lt_of_le_of_lt hle hρlt
  have hfcos_ne : fcos (I := I) (M := M) q y ≠ -1 ∧ fcos (I := I) (M := M) q y ≠ 1 := by
    have hcos : fcos (I := I) (M := M) q y = Real.cos (rdist (I := I) (M := M) q y) := rfl
    constructor
    · rw [hcos]
      intro h
      have h' : Real.cos (rdist (I := I) (M := M) q y) = Real.cos Real.pi := by
        rw [h, Real.cos_pi]
      have := Real.strictAntiOn_cos.injOn ⟨hy0.le, hdpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ h'
      linarith
    · rw [hcos]
      intro h
      have h' : Real.cos (rdist (I := I) (M := M) q y) = Real.cos 0 := by
        rw [h, Real.cos_zero]
      have := Real.strictAntiOn_cos.injOn ⟨hy0.le, hdpi.le⟩ ⟨le_refl 0, Real.pi_pos.le⟩ h'
      linarith
  have hcos_sm : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.arccos
      (fcos (I := I) (M := M) q y) :=
    (Real.contDiffAt_arccos hfcos_ne.1 hfcos_ne.2).contMDiffAt
  have harccos_sm : CMDiffAt ∞
      (fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z)) y :=
    ContMDiffAt.comp (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := fcos (I := I) (M := M) q) (g := Real.arccos) y hcos_sm hsm
  have hev : (fun z : M ↦ rdist (I := I) (M := M) q z) =ᶠ[𝓝 y]
      (fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z)) := by
    have hcont := Work.Diff.C.rdist_continuous (I := I) (M := M) q
    have h1 : ∀ᶠ z in 𝓝 y, 0 < rdist (I := I) (M := M) q z :=
      hcont.continuousAt (isOpen_Ioi.mem_nhds hy0)
    have h2 : ∀ᶠ z in 𝓝 y, rdist (I := I) (M := M) q z < Real.pi :=
      hcont.continuousAt (isOpen_Iio.mem_nhds hdpi)
    filter_upwards [h1, h2] with z hz1 hz2
    show rdist (I := I) (M := M) q z = Real.arccos (fcos (I := I) (M := M) q z)
    rw [show fcos (I := I) (M := M) q z = Real.cos (rdist (I := I) (M := M) q z) from rfl,
      Real.arccos_cos hz1.le hz2.le]
  exact harccos_sm.congr_of_eventuallyEq hev

/-- The distance from `q` to `gam t` is smooth at `gam t`, for `0 < t ≤ rho0`. -/
lemma tc_sm_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ rho0 c) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (tcGam (cov := cov) hmet q v t) :=
  csm_rdist_of_le_rho hc0 hc1 hsmC
    (q := q) (y := tcGam (cov := cov) hmet q v t)
    (by rw [tc_rdist_gam (cov := cov) hmet htor hcut hvn ht0 ht]; exact ht0)
    (by rw [tc_rdist_gam (cov := cov) hmet htor hcut hvn ht0 ht]; exact ht)

/-- The distance from `gam T` to `gam s` is smooth at `gam s`, for `0 < s < T ≤ rho0`. -/
lemma tc_sm_bwd (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {T s : ℝ} (hT : T ≤ rho0 c) (hT0 : 0 < T)
    (hs : 0 < s) (hsT : s < T) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v T) z)
      (tcGam (cov := cov) hmet q v s) := by
  have hTpos : 0 < T - s := sub_pos.mpr hsT
  have hle : T - s ≤ rho0 c := by linarith
  refine csm_rdist_of_le_rho hc0 hc1 hsmC
    (q := tcGam (cov := cov) hmet q v T) (y := tcGam (cov := cov) hmet q v s) ?_ ?_
  · rw [tc_rdist_bwd (cov := cov) hmet htor hcut hvn hT hT0 hs.le hsT]; exact hTpos
  · rw [tc_rdist_bwd (cov := cov) hmet htor hcut hvn hT hT0 hs.le hsT]; exact hle

/-- The eikonal identity at `gam t`. -/
lemma tc_eik_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ rho0 c) :
    Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v t))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v t)) = 1 :=
  Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
    (q := q) (x := tcGam (cov := cov) hmet q v t)
    (by rw [tc_rdist_gam (cov := cov) hmet htor hcut hvn ht0 ht]; exact ne_of_gt ht0)
    (tc_sm_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn ht0 ht)

/-! ## The covariant derivative under a reversal of the parametrisation -/

/-- **The covariant derivative along a curve is compatible with the reversal of the
parametrisation** `s ↦ T - s`: the covariant derivative flips sign. -/
theorem covAlong_comp_sub (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {T t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (T - t - 1) (T - t + 1)))
    (hne : Submission.Geodesic.curveVelocity (I := I) γ (T - t) ≠ 0)
    (hV : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V (T - t)) :
    Submission.JacobiGlobal.covAlong cov (γ := fun s : ℝ => γ (T - s))
        (fun s : ℝ => V (T - s)) t
      = - Submission.JacobiGlobal.covAlong cov (γ := γ) V (T - t) := by
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ := Submission.JacobiGlobal.exists_section_of_smoothAlongAt (I := I)
    hγ hne hV
  have hmem : ∀ s : ℝ, T - s ∈ Set.Ioo (T - t - 1) (T - t + 1) ↔ s ∈ Set.Ioo (t - 1) (t + 1) := by
    intro s
    simp only [Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hγ' : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => γ (T - s)) (Set.Ioo (t - 1) (t + 1)) := by
    have haff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => T - s) :=
      contMDiff_const.sub contMDiff_id
    have h := hγ.comp haff.contMDiffOn (fun s hs => (hmem s).mpr hs)
    simpa only [Function.comp_def] using h
  have hmd : MDifferentiableAt 𝓘(ℝ) I γ (T - t) :=
    (hγ.contMDiffAt (isOpen_Ioo.mem_nhds (by constructor <;> linarith))).mdifferentiableAt
      (by decide)
  have hvel : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => γ (T - s)) t
      = - Submission.Geodesic.curveVelocity (I := I) γ (T - t) := by
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -1) (d := T)
      (t := t) (by simpa only [show (-1 : ℝ) * t + T = T - t from by ring] using hmd)
    have hfun : (fun s : ℝ => γ ((-1) * s + T)) = (fun s : ℝ => γ (T - s)) := by
      funext s
      rw [show (-1 : ℝ) * s + T = T - s from by ring]
    rw [hfun] at h
    rw [h, neg_one_smul]
    rw [show (-1 : ℝ) * t + T = T - t from by ring]
  have hne' : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => γ (T - s)) t ≠ 0 := by
    rw [hvel]; exact neg_ne_zero.mpr hne
  have hV' : Submission.JacobiGlobal.SmoothAlongAt (I := I) (fun s : ℝ => γ (T - s))
      (fun s : ℝ => V (T - s)) t := by
    obtain ⟨U, hUopen, htU, hUsrc, hVcd⟩ := hV
    refine ⟨{s : ℝ | T - s ∈ U}, ?_, htU, ?_, ?_⟩
    · exact hUopen.preimage (continuous_const.sub continuous_id)
    · intro s hs; exact hUsrc (T - s) hs
    · have hcomp : Submission.JacobiCoords.chartCoords (I := I) ((fun s : ℝ => γ (T - s)) t)
            (fun s : ℝ => γ (T - s)) (fun s : ℝ => V (T - s))
          = (fun s : ℝ => Submission.JacobiCoords.chartCoords (I := I) (γ (T - t)) γ V (T - s)) := by
        funext s
        rfl
      rw [hcomp]
      exact hVcd.comp (((contDiff_const.sub contDiff_id) : ContDiff ℝ ∞ (fun s : ℝ => T - s)).contDiffOn)
        (fun s hs => hs)
  have h𝒱ev' : ∀ᶠ s in 𝓝 t, 𝒱 ((fun s : ℝ => γ (T - s)) s) = (fun s : ℝ => V (T - s)) s := by
    have hc : Filter.Tendsto (fun s : ℝ => T - s) (𝓝 t) (𝓝 (T - t)) :=
      (continuous_const.sub continuous_id).tendsto t
    exact hc.eventually h𝒱ev
  rw [Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor hγ' hne' hV' h𝒱sm h𝒱ev',
      Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor hγ hne hV h𝒱sm h𝒱ev]
  rw [hvel, map_neg]

/-! ## Pairings with an explicit point

`Inner.inner ℝ a b` chooses the metric instance from the *type* of `a`, i.e. from the (syntactic)
point at which the tangent vector lives; this makes rewrites along a *propositional* equality of
points fragile.  We therefore write the pairings in the explicit form
`(g).inner X a b` (`tcIn X a b`), where the point is an ordinary argument. -/

/-- The metric pairing of two tangent vectors, with the base point as an *explicit* argument.  The
argument type is written `TangentSpace I x` so that all the section variables are determined (the
type is definitionally `E`, so any element of `E` may be passed). -/
noncomputable def tcIn (X : M) (a b : TangentSpace I X) : ℝ :=
  ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner X a b

lemma tcIn_eq (X : M) (a b : TangentSpace I X) : tcIn X a b = Inner.inner ℝ a b := rfl

lemma tcIn_pt {X Y : M} (h : X = Y) (a b : E) :
    tcIn X (show TangentSpace I X from a) (show TangentSpace I X from b)
      = tcIn Y (show TangentSpace I Y from a) (show TangentSpace I Y from b) := by
  subst h; rfl

@[simp] lemma tcIn_zero_left (X : M) (b : TangentSpace I X) : tcIn X 0 b = 0 := by
  rw [tcIn_eq, inner_zero_left]

@[simp] lemma tcIn_zero_right (X : M) (a : TangentSpace I X) : tcIn X a 0 = 0 := by
  rw [tcIn_eq, inner_zero_right]

lemma tcIn_add_left (X : M) (a a' b : TangentSpace I X) :
    tcIn X (a + a') b = tcIn X a b + tcIn X a' b := by
  rw [tcIn_eq, tcIn_eq, tcIn_eq, inner_add_left]

lemma tcIn_add_right (X : M) (a b b' : TangentSpace I X) :
    tcIn X a (b + b') = tcIn X a b + tcIn X a b' := by
  rw [tcIn_eq, tcIn_eq, tcIn_eq, inner_add_right]

lemma tcIn_smul_left (X : M) (c : ℝ) (a b : TangentSpace I X) :
    tcIn X (c • a) b = c * tcIn X a b := by
  rw [tcIn_eq, tcIn_eq, real_inner_smul_left]

lemma tcIn_smul_right (X : M) (c : ℝ) (a b : TangentSpace I X) :
    tcIn X a (c • b) = c * tcIn X a b := by
  rw [tcIn_eq, tcIn_eq, real_inner_smul_right]

lemma tcIn_symm (X : M) (a b : TangentSpace I X) : tcIn X a b = tcIn X b a := by
  rw [tcIn_eq, tcIn_eq]; exact (real_inner_comm _ _).symm

lemma tcIn_nonneg (X : M) (a : TangentSpace I X) : 0 ≤ tcIn X a a := by
  rw [tcIn_eq, real_inner_self_eq_norm_sq]; positivity

lemma norm_sq_eq_tcIn (X : M) (a : TangentSpace I X) : ‖a‖ ^ 2 = tcIn X a a := by
  rw [tcIn_eq, real_inner_self_eq_norm_sq]

lemma tcGam_eq (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ) :
    tcGam (cov := cov) hmet q v t = Submission.GlobalExp.GExp (cov := cov) hmet q (t • v) := rfl

lemma tcVel_eq (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ) :
    (show E from tcVel (cov := cov) hmet q v t)
      = (show E from Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t) := rfl

lemma smul_eq_of_smul_eq {G : Type*} [AddCommGroup G] [Module ℝ G] {t : ℝ} (ht : t ≠ 0)
    {a b : G} (h : t • a = t • b) : a = b := by
  have h2 := congrArg (fun z : G => t⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ ht, one_smul] using h2


/-- **`covAlong` depends only on the values of the curve and of the field** (a public copy of the
private lemma used in the workspace). -/
theorem covAlong_congr_curve {γ₁ γ₂ : ℝ → M} (h : γ₁ = γ₂)
    {V₁ : (t : ℝ) → TangentSpace I (γ₁ t)} {V₂ : (t : ℝ) → TangentSpace I (γ₂ t)}
    (hV : ∀ t : ℝ, (show E from V₁ t) = (show E from V₂ t)) (d : ℝ) :
    Submission.JacobiGlobal.covAlong cov V₁ d = Submission.JacobiGlobal.covAlong cov V₂ d := by
  subst h
  rw [show V₁ = V₂ from funext hV]

end Work.Diff.C.geoCrux.Port
