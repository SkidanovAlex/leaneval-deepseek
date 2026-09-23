import Submission.XuStep
import Submission.CutTime
import Submission.LensSync
import Submission.InjBall

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.CutTime

namespace Submission.SegmentDomain

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The cut time bounds any meeting of two distinct minimising rays.**  Let `ξ ≠ η` be two unit
directions at `p` whose rays are *both* minimising at time `m > 0` and meet there
(`GExp p (m•ξ) = GExp p (m•η)`).  Then the ray of `ξ` ceases to be minimising no later than `m`:
`cutTime p ξ ≤ m`.

This is the classical statement "at a point reached by two distinct minimising geodesics of the same
length, the ray is past its cut point" — the first structural fact about the cut locus.  Proof: if
`m < cutTime p ξ`, the sync lemma (`LensSync.eq_GExp_of_minimising_pair`) makes the two rays agree on
the whole interval `(m, cutTime p ξ)`; geodesic uniqueness (`eqOn_Ioo_of_isGeodesicAt_of_eq`) applied
at an interior point of that interval upgrades this to agreement on a *neighbourhood of `m`*, so the
two velocities at `m` coincide — contradicting `XuStep.velocity_ne_of_meet`. -/
theorem cutTime_le_of_meet (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hne : ξ ≠ η)
    {m : ℝ} (hm : 0 < m)
    (hξmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m)
    (hηmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η)) = ENNReal.ofReal m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η)) :
    cutTime (I := I) hmet p ξ ≤ m := by
  classical
  refine le_of_not_gt (fun hlt => ?_)
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  set τ : ℝ := cutTime (I := I) hmet p ξ with hτdef
  -- the two rays agree on `(m, τ)`
  have hagree : ∀ t ∈ Ioo m τ, GExp (cov := cov) hmet p (t • ξ)
      = GExp (cov := cov) hmet p (t • η) := by
    intro t ht
    have htmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ))
        = ENNReal.ofReal t :=
      ((mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ).mpr
        ⟨le_trans hm.le ht.1.le, ht.2.le⟩).2
    exact Submission.LensSync.eq_GExp_of_minimising_pair (cov := cov) hmet htor hξ hη hne hm
      ht.1.le hmeet hξmin htmin
  -- an interior point of that interval and the velocities there
  have hmid : (m + τ) / 2 ∈ Ioo m τ := ⟨by linarith, by linarith⟩
  have hev : (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ))
      =ᶠ[𝓝 ((m + τ) / 2)] (fun r : ℝ => GExp (cov := cov) hmet p (r • η)) := by
    filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with r hr
    exact hagree r hr
  have hvelmid : curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ)) ((m + τ) / 2)
      = curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (r • η)) ((m + τ) / 2) :=
    Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev
  -- geodesic uniqueness on `(m - 1, τ + 1)`
  have hEqOn := Submission.GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov)
    (a := m - 1) (b := τ + 1)
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne).mono (Set.subset_univ _))
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hηne).mono (Set.subset_univ _))
    (fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t)
    (fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hηne t)
    (fun t _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne t)
    (fun t _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hηne t)
    (show (m + τ) / 2 ∈ Ioo (m - 1) (τ + 1) from ⟨by linarith, by linarith⟩)
    (hagree ((m + τ) / 2) hmid) hvelmid
  -- hence agreement on a neighbourhood of `m`, and equal velocities at `m`
  have hm_nhds : (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ))
      =ᶠ[𝓝 m] (fun r : ℝ => GExp (cov := cov) hmet p (r • η)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : m - 1 < m) (by linarith : m < τ + 1)] with r hr
    exact hEqOn hr
  have hvelm : curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ)) m
      = curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (r • η)) m :=
    Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hm_nhds
  exact (Submission.XuStep.velocity_ne_of_meet (cov := cov) hmet hξne hηne hm hmeet hne) hvelm

/-- **The tangential segment domain** at `p`: the set of tangent vectors `v` whose ray is
*strictly* minimising at `‖v‖` (i.e. the vectors shorter than the cut time of their direction),
together with `0`.  This is Xu's `D̃_p = {t v : 0 ≤ t < σ(v), ‖v‖ = 1}` (arXiv:1401.5549). -/
def segmentDomain (hmet : IsMetricCompatible cov) (p : M) : Set (TangentSpace I p) :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, ‖v‖ < cutTime (I := I) hmet p (unitOf v hv)}

theorem zero_mem_segmentDomain (hmet : IsMetricCompatible cov) (p : M) :
    (0 : TangentSpace I p) ∈ segmentDomain hmet p := Or.inl rfl

theorem mem_segmentDomain_iff (hmet : IsMetricCompatible cov) (p : M)
    (v : TangentSpace I p) :
    v ∈ segmentDomain hmet p ↔ v = 0 ∨ ∃ hv : v ≠ 0, ‖v‖ < cutTime (I := I) hmet p (unitOf v hv) :=
  Iff.rfl

theorem mem_segmentDomain_of_norm_lt (hmet : IsMetricCompatible cov) {p : M} {v : TangentSpace I p}
    (hv : v ≠ 0) (h : ‖v‖ < cutTime (I := I) hmet p (unitOf v hv)) :
    v ∈ segmentDomain hmet p := Or.inr ⟨hv, h⟩

/-- **Vectors of the segment domain are minimising**: `d(p, GExp p v) = ‖v‖`. -/
theorem edist_GExp_eq_norm_of_mem_segmentDomain (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {p : M} {v : TangentSpace I p} (hv : v ∈ segmentDomain hmet p) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖v‖ := by
  rcases mem_segmentDomain_iff (I := I) hmet p v |>.mp hv with h0 | ⟨hne, hlt⟩
  · subst h0
    rw [GExp_zero, Manifold.riemannianEDist_self, norm_zero, ENNReal.ofReal_zero]
  · have hξ : ‖unitOf v hne‖ = 1 := unitOf_norm v hne
    have hmem : ‖v‖ ∈ minimisingSet (I := I) hmet p (unitOf v hne) :=
      (mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ).mpr
        ⟨norm_nonneg v, hlt.le⟩
    have hsm : ‖v‖ • unitOf v hne = v := by
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul]
    have h := hmem.2
    rw [hsm] at h
    exact h

/-- **The injectivity ball lies in the segment domain.** -/
theorem ball_subset_segmentDomain (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {p : M} {ρ : ℝ} (hinj : InjAtLeast hmet p ρ) :
    Metric.ball (0 : TangentSpace I p) ρ ⊆ segmentDomain hmet p := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  rcases eq_or_ne v 0 with h0 | hne
  · exact Or.inl h0
  · refine mem_segmentDomain_of_norm_lt (I := I) hmet hne ?_
    exact lt_of_lt_of_le hv (injAtLeast_le_cutTime (I := I) (cov := cov) hmet htor hinj
      (unitOf_norm v hne))

/-- **THE SEGMENT-DOMAIN STATEMENT.**  The global exponential map `GExp p` is **injective** on the
tangential segment domain `D̃_p`.  (Classically: `exp_p` is a diffeomorphism from `D̃_p` onto
`M ∖ C_p`; injectivity is the part needed for the *unique lifting* of curves in Klingenberg's
lemma.)

Proof: two vectors of `D̃_p` with the same image are both minimising, hence have equal norms
`m = d(p, ·)`; if the two unit directions differed, `cutTime_le_of_meet` would give
`cutTime p ξ ≤ m = ‖v‖`, contradicting `‖v‖ < cutTime p ξ` from membership in `D̃_p`. -/
theorem injOn_GExp_segmentDomain (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] (p : M) :
    Set.InjOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
      (segmentDomain hmet p) := by
  intro u hu v hv huv
  change GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v at huv
  rcases mem_segmentDomain_iff (I := I) hmet p u |>.mp hu with h0 | ⟨hune, hult⟩
  · subst h0
    rw [GExp_zero] at huv
    rcases mem_segmentDomain_iff (I := I) hmet p v |>.mp hv with h0' | ⟨hvne, hvlt⟩
    · exact h0'.symm
    · have hmin := edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor
        (hv := mem_segmentDomain_of_norm_lt (I := I) hmet hvne hvlt)
      have hz : ENNReal.ofReal ‖v‖ = 0 := by
        rw [← hmin, ← huv, Manifold.riemannianEDist_self]
      exact absurd (norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (norm_nonneg v))) hvne
  · rcases mem_segmentDomain_iff (I := I) hmet p v |>.mp hv with h0' | ⟨hvne, hvlt⟩
    · subst h0'
      rw [GExp_zero] at huv
      have hmin := edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor
        (hv := mem_segmentDomain_of_norm_lt (I := I) hmet hune hult)
      have hz : ENNReal.ofReal ‖u‖ = 0 := by
        rw [← hmin, huv, Manifold.riemannianEDist_self]
      exact absurd (norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (norm_nonneg u))) hune
    · have hminu := edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor
        (hv := mem_segmentDomain_of_norm_lt (I := I) hmet hune hult)
      have hminv := edist_GExp_eq_norm_of_mem_segmentDomain (cov := cov) hmet htor
        (hv := mem_segmentDomain_of_norm_lt (I := I) hmet hvne hvlt)
      have hnorm : ‖u‖ = ‖v‖ := by
        have h : ENNReal.ofReal ‖u‖ = ENNReal.ofReal ‖v‖ := by
          rw [← hminu, ← hminv, huv]
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg u) (norm_nonneg v)).mp h
      have hsm_u : ‖u‖ • unitOf u hune = u := by
        rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hune), one_smul]
      have hsm_v : ‖v‖ • unitOf v hvne = v := by
        rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
      have hmu : 0 < ‖u‖ := norm_pos_iff.mpr hune
      by_cases hunit : unitOf u hune = unitOf v hvne
      · calc u = ‖u‖ • unitOf u hune := hsm_u.symm
          _ = ‖v‖ • unitOf v hvne := by rw [hnorm, hunit]
          _ = v := hsm_v
      · have hξ : ‖unitOf u hune‖ = 1 := unitOf_norm u hune
        have hη : ‖unitOf v hvne‖ = 1 := unitOf_norm v hvne
        have h2 : ‖u‖ • unitOf v hvne = v := by rw [hnorm, hsm_v]
        have hmeet : GExp (cov := cov) hmet p (‖u‖ • unitOf u hune)
            = GExp (cov := cov) hmet p (‖u‖ • unitOf v hvne) := by
          rw [hsm_u, h2, huv]
        have hξmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖u‖ • unitOf u hune))
            = ENNReal.ofReal ‖u‖ := by
          simpa only [hsm_u] using hminu
        have hηmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖u‖ • unitOf v hvne))
            = ENNReal.ofReal ‖u‖ := by
          simpa only [hnorm, hsm_v] using hminv
        have hkey := cutTime_le_of_meet (cov := cov) hmet htor hξ hη hunit hmu hξmin hηmin hmeet
        exact absurd hkey (not_le.mpr hult)

/-- **Every point of the injectivity ball has a unique *segment-domain* vector.**  This is the form of
the segment-domain statement that Xu's first paragraph produces ("we are able to lift `γ` to
`(exp_p|D̃_p)⁻¹ ∘ γ` *uniquely* in the tangential segment domain"): a point `y` with
`d(p,y) < ρ ≤ inj(p)` is `GExp p v` for exactly one `v` of the segment domain. -/
theorem exists_unique_segmentDomain_vec (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ρ : ℝ} (hinj : InjAtLeast hmet p ρ) {y : M}
    (hy : Manifold.riemannianEDist I p y < ENNReal.ofReal ρ) :
    ∃! v : TangentSpace I p, v ∈ segmentDomain hmet p ∧ GExp (cov := cov) hmet p v = y := by
  obtain ⟨v, hvlt, hvG⟩ := Submission.InjBall.exists_tangent_of_edist_lt (cov := cov) hmet htor hy
  have hmem : v ∈ segmentDomain hmet p :=
    ball_subset_segmentDomain (I := I) (cov := cov) hmet htor hinj
      (by rw [Metric.mem_ball, dist_zero_right]; exact hvlt)
  refine ⟨v, ⟨hmem, hvG⟩, ?_⟩
  rintro w ⟨hwmem, hwG⟩
  exact injOn_GExp_segmentDomain (cov := cov) hmet htor p hwmem hmem (by
    change GExp (cov := cov) hmet p w = GExp (cov := cov) hmet p v
    rw [hwG, hvG])

/-- **The image of the segment domain contains the injectivity ball.** -/
theorem ball_subset_image_segmentDomain (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ρ : ℝ} (hinj : InjAtLeast hmet p ρ) :
    {y : M | Manifold.riemannianEDist I p y < ENNReal.ofReal ρ} ⊆
      (fun v : TangentSpace I p => GExp (cov := cov) hmet p v) '' segmentDomain hmet p := by
  intro y hy
  obtain ⟨v, hvlt, hvG⟩ := Submission.InjBall.exists_tangent_of_edist_lt (cov := cov) hmet htor
    (y := y) (m := ρ) hy
  refine ⟨v, ?_, hvG⟩
  refine ball_subset_segmentDomain (I := I) (cov := cov) hmet htor hinj ?_
  rw [Metric.mem_ball, dist_zero_right]
  exact hvlt

end

end Submission.SegmentDomain
