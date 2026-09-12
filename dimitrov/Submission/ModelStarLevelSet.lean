import Mathlib
import Submission.ModelStarPotential
import Submission.ModelStarHarmMeasure

/-!
# ModelStarLevelSet -- the level sets of the model boundary map are finite,
# hence the harmonic measure of the model star is atomless

STATUS: research isolate (NOT imported by `Submission.lean`).

For the model map `F = modelF z₀ r` with `F(z)/z → 1` and `M = F '' unitCircle`,
the harmonic measure `μ₀ = F_*(dθ/2π)` (`Submission.ModelStarHarmMeasure`) is
carried by `M`.  This module proves that `μ₀` has no atoms:

  * `levelSetU z₀ r y = {u | ‖u‖ = 1 ∧ diskPhi z₀ r u = y * u}` is FINITE for
    every `y` (for `y ∈ M ∖ {0}` because every point of the level set is an
    ISOLATED zero of the analytic function `h_y = diskPhi - y·id` on the circle,
    the sphere being compact; for `y = 0` it is the junction set; for `y ∉ M`
    it is empty);
  * consequently `Z_y = {z | ‖z‖ = 1 ∧ F z = y}` is finite;
  * hence `μ₀ {y} = 0` for every `y : ℂ`, i.e. `NullSingletonClass μ₀`.
-/

noncomputable section

open scoped Real BigOperators Topology ENNReal
open Filter Set Complex MeasureTheory

namespace Submission.ModelStarLevelSet

open Submission.ModelStarMap
open Submission.ModelStarDisk (diskPhi diskPhi_zero)
open Submission.ModelStarPotential (circleBad diskPhi_inv_eq_zero hx hx_apply hx_ne_zero_of_mem_ball
  circleBad_spec analyticAt_diskPhi_of_not_mem_bad continuousOn_hx)
open Submission.ModelStarExterior (unitCircle modelStarImage mem_circle)
open Submission.ModelStarHarmMeasure (circleMeasure harmMeasure circleMeasure_apply_Ioc harmMeasure_apply
  meas_circleMap_modelF)

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-- The level set of the disk model `diskPhi z₀ r` on the unit circle. -/
def levelSetU (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (y : ℂ) : Set ℂ :=
  {u : ℂ | ‖u‖ = 1 ∧ diskPhi z₀ r u = y * u}

lemma mem_levelSetU {y u : ℂ} :
    u ∈ levelSetU z₀ r y ↔ ‖u‖ = 1 ∧ diskPhi z₀ r u = y * u := Iff.rfl

/-- Membership in `levelSetU` is exactly the vanishing of `h_y`. -/
lemma levelSetU_eq (y : ℂ) :
    levelSetU z₀ r y = {u : ℂ | ‖u‖ = 1 ∧ hx z₀ r y u = 0} := by
  ext u
  simp only [mem_levelSetU, Set.mem_setOf_eq, hx_apply, sub_eq_zero]

lemma levelSetU_ne_zero {y u : ℂ} (hu : u ∈ levelSetU z₀ r y) : u ≠ 0 := by
  have h1 : ‖u‖ = 1 := hu.1
  intro h
  rw [h, norm_zero] at h1
  norm_num at h1

/-- At `y = 0` the level set is the set of junction points. -/
lemma levelSetU_zero (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    levelSetU z₀ r 0 = (circleBad z₀ : Set ℂ) := by
  ext u
  rw [mem_levelSetU]
  constructor
  · rintro ⟨h1, h2⟩
    rw [zero_mul, diskPhi] at h2
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h2
    rw [Submission.ModelStarDisk.diskFactor] at hk
    have hk' : 1 - z₀ k * u = 0 := by
      by_contra h
      exact absurd hk (Complex.cpow_ne_zero_iff.mpr (Or.inl h))
    have hzk : z₀ k ≠ 0 := Submission.ModelStarPotential.junction_ne_zero hunit k
    have hmul : z₀ k * u = 1 := (sub_eq_zero.mp hk').symm
    have hueq : u = (z₀ k)⁻¹ := by
      calc u = (z₀ k)⁻¹ * (z₀ k * u) := by rw [← mul_assoc, inv_mul_cancel₀ hzk, one_mul]
        _ = (z₀ k)⁻¹ * 1 := by rw [hmul]
        _ = (z₀ k)⁻¹ := mul_one _
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hueq.symm⟩
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨k, -, hk⟩
    rw [← hk]
    refine ⟨?_, ?_⟩
    · rw [norm_inv, hunit k, inv_one]
    · rw [diskPhi_inv_eq_zero hunit hr k, zero_mul]

/-- For `y ∉ M` the level set is empty. -/
lemma levelSetU_eq_empty_of_notMem {y : ℂ} (hy : y ∉ modelStarImage z₀ r) :
    levelSetU z₀ r y = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  obtain ⟨h1, h2⟩ := hu
  have hu0 : u ≠ 0 := levelSetU_ne_zero ⟨h1, h2⟩
  have h3 : modelF z₀ r u⁻¹ = y := by
    have h := Submission.ModelStarDisk.mul_modelF_inv_eq z₀ r hu0
    rw [h2, mul_comm y u] at h
    exact mul_left_cancel₀ hu0 h
  refine hy ⟨u⁻¹, ?_, h3⟩
  rw [mem_circle, norm_inv, h1, inv_one]



/-! ## §3  Isolation and finiteness of the level sets -/

/-- Every point of `levelSetU z₀ r y` is isolated in it, for `y ∈ M`, `y ≠ 0`
(the analytic function `h_y = diskPhi - y·id` has only isolated zeros on the
circle). -/
lemma exists_isOpen_inter_eq_singleton
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {y : ℂ} (hyM : y ∈ modelStarImage z₀ r) (hy0 : y ≠ 0)
    {u : ℂ} (hu : u ∈ levelSetU z₀ r y) :
    ∃ U : Set ℂ, IsOpen U ∧ u ∈ U ∧ U ∩ levelSetU z₀ r y = {u} := by
  have hu1 : ‖u‖ = 1 := hu.1
  have hu2 : hx z₀ r y u = 0 := by rw [hx_apply, hu.2, sub_self]
  have hu0 : u ≠ 0 := levelSetU_ne_zero hu
  have hu_bad : u ∉ circleBad z₀ := by
    intro hb
    have hb' : u ∈ circleBad z₀ := hb
    rcases Finset.mem_image.mp hb' with ⟨k, -, hk⟩
    have hzero : diskPhi z₀ r u = 0 := by rw [← hk]; exact diskPhi_inv_eq_zero hunit hr k
    have : y * u = 0 := by rw [← hu.2, hzero]
    exact hy0 ((mul_eq_zero.mp this).resolve_right hu0)
  have hB : ∀ b ∈ circleBad z₀, b ∈ Metric.sphere (0 : ℂ) 1 ∧ hx z₀ r y b ≠ 0 :=
    circleBad_spec hunit hr hy0
  have han : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z ∉ circleBad z₀ →
      AnalyticAt ℂ (hx z₀ r y) z :=
    fun z hz hzB => (analyticAt_diskPhi_of_not_mem_bad hunit hz hzB).sub (by fun_prop)
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, hx z₀ r y z ≠ 0 :=
    fun z hz => hx_ne_zero_of_mem_ball hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hyM hz
  have hnot : ¬ ∀ᶠ w in nhds u, hx z₀ r y w = 0 :=
    Commons.Analysis.Complex.not_eventually_zero_at_sphere_point (hx z₀ r y) (circleBad z₀)
      hB han hne (by rw [Metric.mem_sphere, dist_zero_right]; exact hu1)
  have hana : AnalyticAt ℂ (hx z₀ r y) u :=
    han u (by simp [Metric.mem_closedBall, hu1]) hu_bad
  have hev : ∀ᶠ w in nhdsWithin u {u}ᶜ, hx z₀ r y w ≠ 0 :=
    (hana.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnot
  rw [eventually_nhdsWithin_iff, Filter.eventually_iff] at hev
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨Metric.ball u ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, ?_⟩
  ext w
  constructor
  · rintro ⟨hwV, hwS⟩
    rw [Set.mem_singleton_iff]
    by_contra hne'
    exact hball hwV hne' (by rw [hx_apply, hwS.2, sub_self])
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨Metric.mem_ball_self hεpos, hu⟩

/-- The level set of the disk model is compact (it is a closed subset of the
circle). -/
lemma isCompact_levelSetU (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (y : ℂ) :
    IsCompact (levelSetU z₀ r y) := by
  have hclosed : IsClosed (levelSetU z₀ r y) := by
    rw [← closure_subset_iff_isClosed]
    intro x hxcl
    have hcl : ∀ ε > 0, ∃ b ∈ levelSetU z₀ r y, dist x b < ε :=
      (Metric.mem_closure_iff).mp hxcl
    have hxsphere : x ∈ Metric.sphere (0 : ℂ) 1 := by
      have h1 : x ∈ closure (Metric.sphere (0 : ℂ) 1) :=
        closure_mono (fun u hu => by rw [Metric.mem_sphere, dist_zero_right]; exact hu.1) hxcl
      rwa [Metric.isClosed_sphere.closure_eq] at h1
    have hx1 : ‖x‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hxsphere
    have hxcb : x ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, hx1]
    have hcont := (continuousOn_hx hunit hr y).continuousWithinAt hxcb
    have h0 : hx z₀ r y x = 0 := by
      by_contra hne0
      have hpos : 0 < ‖hx z₀ r y x‖ := norm_pos_iff.mpr hne0
      obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.mp hcont) ‖hx z₀ r y x‖ hpos
      obtain ⟨b, hbS, hbd⟩ := hcl δ hδpos
      have hbcb : b ∈ Metric.closedBall (0 : ℂ) 1 := by
        simp [Metric.mem_closedBall, hbS.1]
      have hb0 : hx z₀ r y b = 0 := by rw [hx_apply, hbS.2, sub_self]
      have hlt := hδ hbcb (by rwa [dist_comm] at hbd)
      rw [hb0, dist_zero_left] at hlt
      exact absurd hlt (lt_irrefl _)
    exact ⟨hx1, sub_eq_zero.mp h0⟩
  refine (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hclosed, ?_⟩
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨1, ?_⟩
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq hu.1

/-- **Finiteness of the level sets of the disk model.** -/
theorem finite_levelSetU
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) (y : ℂ) :
    (levelSetU z₀ r y).Finite := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [levelSetU_zero hunit hr]
    exact (circleBad z₀).finite_toSet
  by_cases hyM : y ∈ modelStarImage z₀ r
  · refine (isCompact_levelSetU hunit hr y).finite ?_
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
    intro a
    obtain ⟨U, hUopen, hUa, hUeq⟩ :=
      exists_isOpen_inter_eq_singleton hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hyM hy0 a.2
    rw [isOpen_induced_iff]
    refine ⟨U, hUopen, ?_⟩
    ext b
    constructor
    · intro hb
      rw [Set.mem_singleton_iff]
      have hmem : (b : ℂ) ∈ U ∩ levelSetU z₀ r y := ⟨hb, b.2⟩
      rw [hUeq] at hmem
      exact Subtype.ext (Set.mem_singleton_iff.mp hmem)
    · intro hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hUa
  · rw [levelSetU_eq_empty_of_notMem hyM]
    exact Set.finite_empty

/-- The level set of the model map on the unit circle. -/
def levelSetZ (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (y : ℂ) : Set ℂ :=
  {z : ℂ | ‖z‖ = 1 ∧ modelF z₀ r z = y}

lemma levelSetZ_finite
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) (y : ℂ) :
    (levelSetZ z₀ r y).Finite := by
  have hsub : levelSetZ z₀ r y ⊆ (fun z : ℂ => z⁻¹) ⁻¹' levelSetU z₀ r y := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz1; norm_num at hz1
    refine ⟨?_, ?_⟩
    · rw [norm_inv, hz1, inv_one]
    · have h := Submission.ModelStarDisk.mul_modelF_inv_eq z₀ r (inv_ne_zero hz0)
      rw [inv_inv, hz2, mul_comm] at h
      exact h.symm
  refine Set.Finite.subset ?_ hsub
  exact (finite_levelSetU hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi y).preimage
    (f := fun z : ℂ => z⁻¹) (by intro a _ b _ hab; exact inv_inj.mp hab)


/-- **The harmonic measure of the model star is atomless.**  Equivalently: the
level sets of the boundary map `θ ↦ F(e^{iθ})` are finite, hence null for the
arclength measure. -/
theorem nullSingletonClass_harmMeasure
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) :
    MeasureTheory.NullSingletonClass (harmMeasure z₀ r) := by
  refine MeasureTheory.NullSingletonClass.mk (fun y => ?_)
  have hfin := levelSetZ_finite hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi y
  have hZnorm : ∀ z ∈ hfin.toFinset, ‖z‖ = 1 := fun z hz => (hfin.mem_toFinset.mp hz).1
  have hzero : MeasureTheory.volume {θ : ℝ | circleMap 0 1 θ ∈ (hfin.toFinset : Set ℂ)} = 0 :=
    Commons.Analysis.Complex.measure_preimage_circleMap_finset hfin.toFinset hZnorm
  have hsub : {θ : ℝ | modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) ∈ ({y} : Set ℂ)}
      ⊆ {θ : ℝ | circleMap 0 1 θ ∈ (hfin.toFinset : Set ℂ)} := by
    intro θ hθ
    have hy : modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) = y := by simpa using hθ
    refine hfin.mem_toFinset.mpr ⟨?_, ?_⟩
    · rw [_root_.norm_circleMap_zero]; norm_num
    · rw [circleMap_zero, Complex.ofReal_one, one_mul]; exact hy
  have hvolA : MeasureTheory.volume
      {θ : ℝ | modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) ∈ ({y} : Set ℂ)} = 0 :=
    MeasureTheory.measure_mono_null hsub hzero
  rw [harmMeasure_apply (measurableSet_singleton y)]
  have hA : MeasurableSet
      {θ : ℝ | modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) ∈ ({y} : Set ℂ)} :=
    (meas_circleMap_modelF z₀ r) (measurableSet_singleton y)
  rw [circleMeasure, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply hA]
  rw [MeasureTheory.measure_mono_null Set.inter_subset_left hvolA, smul_zero]


/-- The `θ`-level sets of `θ ↦ F(e^{iθ})` are null for the arclength measure
(the version in the `circleMap` parametrisation). -/
lemma volume_setOf_modelF_circleMap_eq
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) (y : ℂ) :
    MeasureTheory.volume {θ : ℝ | modelF z₀ r (circleMap 0 1 θ) = y} = 0 := by
  have hfin := levelSetZ_finite hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi y
  have hZnorm : ∀ z ∈ hfin.toFinset, ‖z‖ = 1 := fun z hz => (hfin.mem_toFinset.mp hz).1
  refine MeasureTheory.measure_mono_null ?_
    (Commons.Analysis.Complex.measure_preimage_circleMap_finset hfin.toFinset hZnorm)
  intro θ hθ
  simp only [Set.mem_setOf_eq] at hθ ⊢
  exact hfin.mem_toFinset.mpr ⟨by rw [_root_.norm_circleMap_zero]; norm_num, hθ⟩

end Submission.ModelStarLevelSet
