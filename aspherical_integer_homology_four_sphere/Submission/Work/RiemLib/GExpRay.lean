import Submission.Work.RiemLib.HingeKey
import Submission.Work.RiemLib.HingeLocal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rays of the global exponential map are minimising, and the dependent hinge comparison

`Submission.GExp.GExp hmet z v` is the endpoint of the unit-speed geodesic segment from `z` in the
direction `v`.  This file proves the elementary **ray bound**

`d(GExp z (a • v), GExp z (b • v)) ≤ |a - b|`  (`‖v‖ = 1`, `0 ≤ a ≤ b`)

by bounding the Riemannian distance by the length of the sub-arc of the ray (which is a sub-arc of a
`geodCurve`, hence `C¹` with unit speed), and deduces the **linearly dependent case** of the hinge
comparison: for `w = v` it is the ray bound, for `w = -v` the triangle inequality through `z`
together with the two half ray bounds.  Together with the linearly independent case this gives the
full `GCompHolds`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.Minimal
open Submission.HingeLocal
open Submission.HingeGlobal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpRay

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The ray bound.**  For a unit vector `v` and `0 ≤ a ≤ b`, the two points of the ray
`s ↦ GExp z (s • v)` are at Riemannian distance at most `b - a`. -/
theorem edist_GExp_smul_le (hmet : IsMetricCompatible cov) (z : M) {v : TangentSpace I z}
    (hv : ‖v‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v)) (GExp (cov := cov) hmet z (b • v))
      ≤ ENNReal.ofReal (b - a) := by
  have hvne : v ≠ 0 := by
    rintro rfl
    simp at hv
  set ξ : TangentSpace I z := unitOf v hvne with hξdef
  have hξnorm : ‖ξ‖ = 1 := unitOf_norm v hvne
  set T : ℝ := max ‖v‖ (b * ‖v‖) with hTdef
  have hTnn : 0 ≤ T := le_trans (norm_nonneg v) (le_max_left _ _)
  set Gp : ℝ → M := geodCurve (cov := cov) hmet T hTnn z ξ hξnorm with hGpdef
  have hgd := geodDelta_pos (cov := cov) hmet
  -- the two endpoints as values of the fixed geodesic segment
  have hGb : GExp (cov := cov) hmet z (b • v) = Gp (b * ‖v‖) :=
    GExp_smul (cov := cov) hmet z hvne hb
  have hGa : GExp (cov := cov) hmet z (a • v) = Gp (a * ‖v‖) := by
    have h1 := GExp_smul (cov := cov) hmet z hvne ha
    have hTa : 0 ≤ max ‖v‖ (a * ‖v‖) := le_trans (norm_nonneg v) (le_max_left _ _)
    have hle : max ‖v‖ (a * ‖v‖) ≤ T :=
      max_le (le_max_left _ _)
        (le_trans (mul_le_mul_of_nonneg_right hab (norm_nonneg v)) (le_max_right _ _))
    have hmem : a * ‖v‖ ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (max ‖v‖ (a * ‖v‖) + geodDelta (cov := cov) hmet) :=
      Set.mem_Ioo.mpr ⟨by linarith [hgd, mul_nonneg ha (norm_nonneg v)],
        by linarith [hgd, le_max_right ‖v‖ (a * ‖v‖)]⟩
    rw [h1]
    exact geodCurve_agree (cov := cov) hmet hTa hTnn hle z ξ hξnorm hmem
  obtain ⟨h0, hv0, hsm, hgeo, hsp⟩ := geodCurve_spec (cov := cov) hmet T hTnn z ξ hξnorm
  have hab' : a * ‖v‖ ≤ b * ‖v‖ := mul_le_mul_of_nonneg_right hab (norm_nonneg v)
  have hsub : Set.Icc (a * ‖v‖) (b * ‖v‖) ⊆
      Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
    intro t ht
    refine Set.mem_Ioo.mpr ⟨by linarith [hgd, mul_nonneg ha (norm_nonneg v), ht.1], ?_⟩
    have h1 : b * ‖v‖ ≤ T := le_max_right _ _
    linarith [ht.2, h1]
  haveI hcontR : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  have hγ : CMDiff[Set.Icc (a * ‖v‖) (b * ‖v‖)] 1 Gp :=
    (hsm.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
  have hdist : Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
      (GExp (cov := cov) hmet z (b • v)) ≤ Manifold.pathELength I Gp (a * ‖v‖) (b * ‖v‖) := by
    have h := Submission.EDist.riemannianEDist_le_pathELength (I := I) (γ := Gp) hγ
      (by rw [← hGa]) (by rw [← hGb]) hab'
    exact h
  -- the length of the sub-arc is `b - a`
  have hlen' : Manifold.pathELength I Gp (a * ‖v‖) (b * ‖v‖)
      = ∫⁻ t in Set.Icc (a * ‖v‖) (b * ‖v‖),
          ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Gp t) (1 : ℝ)‖ₑ :=
    Manifold.pathELength_eq_lintegral_mfderiv_Icc
  have hbnd : (∫⁻ t in Set.Icc (a * ‖v‖) (b * ‖v‖),
        ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Gp t) (1 : ℝ)‖ₑ)
      ≤ ENNReal.ofReal (b * ‖v‖ - a * ‖v‖) := by
    have hone : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (a * ‖v‖) (b * ‖v‖))),
        ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Gp t) (1 : ℝ)‖ₑ ≤ ENNReal.ofReal 1 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      have h1 : ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Gp t) (1 : ℝ)‖ₑ
          = ENNReal.ofReal ‖curveVelocity (I := I) Gp t‖ := by
        change ‖curveVelocity (I := I) Gp t‖ₑ = _
        rw [Submission.Minimal.enorm_eq_ofReal_norm]
      rw [h1, hsp t (hsub ht), ENNReal.ofReal_one]
    calc (∫⁻ t in Set.Icc (a * ‖v‖) (b * ‖v‖),
          ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Gp t) (1 : ℝ)‖ₑ)
        ≤ ∫⁻ _ in Set.Icc (a * ‖v‖) (b * ‖v‖), ENNReal.ofReal 1 :=
          MeasureTheory.lintegral_mono_ae hone
      _ = ENNReal.ofReal 1 * MeasureTheory.volume (Set.Icc (a * ‖v‖) (b * ‖v‖)) :=
          MeasureTheory.setLIntegral_const _ _
      _ = ENNReal.ofReal 1 * ENNReal.ofReal (b * ‖v‖ - a * ‖v‖) := by rw [Real.volume_Icc]
      _ = ENNReal.ofReal (b * ‖v‖ - a * ‖v‖) := by rw [ENNReal.ofReal_one, one_mul]
  have hlen : Manifold.pathELength I Gp (a * ‖v‖) (b * ‖v‖) ≤ ENNReal.ofReal (b - a) := by
    refine le_trans (le_of_eq hlen') ?_
    simpa only [hv, mul_one] using hbnd
  calc Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • v))
      ≤ Manifold.pathELength I Gp (a * ‖v‖) (b * ‖v‖) := hdist
    _ ≤ ENNReal.ofReal (b - a) := hlen

/-- **The ray bound, zero case.**  `d(z, GExp z (a • v)) ≤ a` for a unit `v` and `a ≥ 0`. -/
theorem edist_GExp_smul_le_zero (hmet : IsMetricCompatible cov) (z : M) {v : TangentSpace I z}
    (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 ≤ a) :
    Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (a • v))
      ≤ ENNReal.ofReal a := by
  have h := edist_GExp_smul_le (cov := cov) hmet z hv (a := 0) (b := a) le_rfl ha ha
  rw [zero_smul, GExp_zero] at h
  simpa using h

/-- **The linearly dependent case of the hinge comparison.**  For unit `v` and `w = ±v` and
`0 < a`, `0 < b`, `a + b ≤ π`, the comparison `HingeCompG` holds. -/
theorem hingeCompG_dependent (hmet : IsMetricCompatible cov) (z : M)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ Real.pi)
    {v w : TangentSpace I z} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hdep : w = v ∨ w = -v) :
    Submission.HingeKey.HingeCompG (cov := cov) hmet z a b v w := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hsub : |a - b| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  rcases hdep with hwv | hwv
  · -- `w = v`: the ray bound
    rw [hwv]
    have hmain : Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • v)) ≤ ENNReal.ofReal |a - b| := by
      rcases le_total a b with hle | hle
      · have h := edist_GExp_smul_le (cov := cov) hmet z hv ha.le hb.le hle
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
        exact h
      · have h := edist_GExp_smul_le (cov := cov) hmet z hv hb.le ha.le hle
        rw [Manifold.riemannianEDist_comm] at h
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        exact h
    have hrhs : modelDist1 (Submission.HingeGlobal.hingeAngle v v) a b = |a - b| := by
      rw [Submission.HingeGlobal.modelDist1, Submission.HingeGlobal.cos_hingeAngle hv hv, hvv,
        mul_one, ← Real.cos_sub]
      exact Submission.HingeLocal.arccos_cos_eq_abs (abs_le.mp hsub).1 (abs_le.mp hsub).2
    rw [Submission.HingeKey.HingeCompG, hrhs]
    exact hmain
  · -- `w = -v`: the triangle inequality through `z`
    rw [hwv]
    have h1 : Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v)) z
        ≤ ENNReal.ofReal a := by
      rw [Manifold.riemannianEDist_comm]
      exact edist_GExp_smul_le_zero (cov := cov) hmet z hv ha.le
    have h2 : Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (b • (-v)))
        ≤ ENNReal.ofReal b :=
      edist_GExp_smul_le_zero (cov := cov) hmet z (by rw [norm_neg]; exact hv) hb.le
    have htri := Manifold.riemannianEDist_triangle (I := I)
      (x := GExp (cov := cov) hmet z (a • v)) (y := z)
      (z := GExp (cov := cov) hmet z (b • (-v)))
    have hmain : Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • (-v))) ≤ ENNReal.ofReal (a + b) := by
      refine htri.trans (le_trans (add_le_add h1 h2) (le_of_eq ?_))
      rw [ENNReal.ofReal_add ha.le hb.le]
    have hnv : ‖(-v : TangentSpace I z)‖ = 1 := by rw [norm_neg]; exact hv
    have hrhs : modelDist1 (Submission.HingeGlobal.hingeAngle v (-v)) a b = a + b := by
      rw [Submission.HingeGlobal.modelDist1,
        Submission.HingeGlobal.cos_hingeAngle hv hnv]
      have hinner : inner ℝ v (-v) = -1 := by
        rw [inner_neg_right, hvv]
      rw [hinner]
      have hcos : Real.cos a * Real.cos b + Real.sin a * Real.sin b * (-1)
          = Real.cos (a + b) := by rw [Real.cos_add]; ring
      rw [hcos]
      exact Real.arccos_cos (by linarith) hab
    rw [Submission.HingeKey.HingeCompG, hrhs]
    exact hmain

end

end Submission.GExpRay
