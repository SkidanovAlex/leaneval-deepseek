import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarDisk
import Submission.ModelStarExterior
import Submission.ModelStarExteriorSep
import Submission.Commons.Analysis.Complex.circleAverage_log_norm_sub
import Submission.Commons.Analysis.Complex.circleAverage_log_norm_of_analytic_off_finite

/-!
# ModelStarPotential -- the logarithmic potential of the harmonic measure of a
# model star vanishes on the star

STATUS: research isolate (NOT imported by `Submission.lean`).

For the model map `F = modelF z₀ r` with `F(z)/z → 1`, let
`M = modelStarImage z₀ r = F '' unitCircle` be the model star and let
`μ₀ := F_*(dθ/2π)` be the pushforward of the normalised arclength on the
circle (the harmonic measure of `M` from `∞`).  Its logarithmic potential is

    `U(x) = ∫₀^{2π} log ‖F(e^{iθ}) - x‖ dθ/2π = Real.circleAverage (fun z => Real.log ‖F z - x‖) 0 1`.

This module proves -- modulo the single analytic input
`Commons.Analysis.Complex.circleAverage_log_norm_of_analytic_off_finite`
("Jensen at the boundary": for `f` continuous on the closed unit ball, holomorphic
on the open ball except at finitely many circle points where it is nonzero, and
nonvanishing on the open ball, `circleAverage (log ‖f‖) 0 1 = log ‖f 0‖`) -- that

    **`U(x) = 0` for every `x ∈ M`.**

This is the input (P3) of the STATUS §119 chain towards `(N1)`:
`(P3)` together with the conditional positive definiteness of the log kernel
(commons `log_kernel_polarization`) and the elementary Fekete bookkeeping
gives the Fekete-root upper bound `FeketeLim M ≤ 1`.

The reduction is: by (P3) (`F '' {1 < ‖z‖} ∩ M = ∅`, PROVED in
`Submission.ModelStarExteriorSep`) the disk-model function
`h_x(u) = diskPhi u - x·u` is nonvanishing on the open unit disk and, for
`x ≠ 0`, nonzero at the (finitely many) junction points `(z₀ k)⁻¹` of the circle;
on the circle `h_x(e^{iθ}) = e^{iθ}(F(e^{-iθ}) - x)`, so its log-average is
exactly `U(x)`, and the boundary-Jensen input gives `U(x) = log ‖h_x 0‖ = 0`.
The case `x = 0` is computed directly from `‖F(z)‖ = ∏_k ‖z - z_k‖^{2 r_k}` on
the circle.
-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set Complex

namespace Submission.ModelStarPotential

open Submission.ModelStarMap
open Submission.ModelStarExterior (modelStarImage)
open Submission.ModelStarDisk (diskPhi diskPhi_zero diskPhi_sub_eq)

variable {s : ℕ} {z₀ : Fin s → ℂ} {r : Fin s → ℝ}

/-- The logarithmic potential of the harmonic measure `F_*(dθ/2π)` of the model
star, evaluated at `x`. -/
noncomputable def potential (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (x : ℂ) : ℝ :=
  Real.circleAverage (fun z : ℂ => Real.log ‖modelF z₀ r z - x‖) 0 1

/-- The real-valued "log of the modulus" of the disk model minus `x·id`, whose
circle average is the potential at `x`. -/
noncomputable def hx (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (x : ℂ) : ℂ → ℂ :=
  fun u => diskPhi z₀ r u - x * u

lemma hx_apply (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (x u : ℂ) :
    hx z₀ r x u = diskPhi z₀ r u - x * u := rfl

/-- On the unit circle `‖h_x u‖ = ‖F(u⁻¹) - x‖`. -/
lemma norm_hx_eq {x u : ℂ} (hu0 : u ≠ 0) (hu : ‖u‖ = 1) :
    ‖hx z₀ r x u‖ = ‖modelF z₀ r u⁻¹ - x‖ := by
  rw [hx_apply, diskPhi_sub_eq z₀ r hu0]
  rw [norm_mul, hu, one_mul]

/-- The circle average of `log ‖h_x‖` equals the potential at `x`. -/
lemma circleAverage_log_hx_eq_potential (x : ℂ) :
    Real.circleAverage (fun u : ℂ => Real.log ‖hx z₀ r x u‖) 0 1 = potential z₀ r x := by
  have hcongr : Real.circleAverage (fun u : ℂ => Real.log ‖hx z₀ r x u‖) 0 1
      = Real.circleAverage (fun u : ℂ => Real.log ‖modelF z₀ r u⁻¹ - x‖) 0 1 := by
    refine Real.circleAverage_congr_sphere ?_
    intro u hu
    have hu1 : ‖u‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hu
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hu1
      exact one_ne_zero hu1.symm
    show Real.log ‖hx z₀ r x u‖ = Real.log ‖modelF z₀ r u⁻¹ - x‖
    rw [norm_hx_eq hu0 hu1]
  rw [hcongr, potential]
  exact Real.circleAverage_zero_one_congr_inv (f := fun z : ℂ => Real.log ‖modelF z₀ r z - x‖)

end Submission.ModelStarPotential

namespace Submission.ModelStarPotential

open Submission.ModelStarMap
open Submission.ModelStarExterior (modelStarImage)
open Submission.ModelStarDisk (diskPhi diskPhi_zero diskPhi_sub_eq)
open Submission.ModelStarPreimageCount (extSet)

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-- The "junction points" of the circle for the disk model: the points
`(z₀ k)⁻¹` where one disk factor vanishes. -/
noncomputable def circleBad (z₀ : Fin s → ℂ) : Finset ℂ :=
  Finset.univ.image (fun k : Fin s => (z₀ k)⁻¹)

lemma junction_ne_zero (hunit : ∀ k, ‖z₀ k‖ = 1) (k : Fin s) : z₀ k ≠ 0 := by
  intro h
  have h1 : (0 : ℝ) = 1 := by rw [← hunit k, h, norm_zero]
  norm_num at h1

/-- `diskPhi` vanishes at every junction point. -/
lemma diskPhi_inv_eq_zero (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (k : Fin s) :
    diskPhi z₀ r (z₀ k)⁻¹ = 0 := by
  have hz0 : z₀ k ≠ 0 := junction_ne_zero hunit k
  have hfac : Submission.ModelStarDisk.diskFactor (z₀ k) (2 * r k) (z₀ k)⁻¹ = 0 := by
    rw [Submission.ModelStarDisk.diskFactor]
    have h1 : 1 - z₀ k * (z₀ k)⁻¹ = 0 := by
      rw [mul_inv_cancel₀ hz0, sub_self]
    rw [h1]
    refine Complex.zero_cpow ?_
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (by linarith [hr k])
  rw [diskPhi]
  exact Finset.prod_eq_zero (Finset.mem_univ k) hfac

/-- Continuity of `h_x = diskPhi - x·id` on the closed unit ball. -/
lemma continuousOn_hx (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (x : ℂ) :
    ContinuousOn (hx z₀ r x) (Metric.closedBall (0 : ℂ) 1) := by
  change ContinuousOn (fun u : ℂ => diskPhi z₀ r u - x * u) (Metric.closedBall (0 : ℂ) 1)
  exact (Submission.ModelStarDisk.continuousOn_diskPhi_closedBall z₀ r hunit hr).sub (by fun_prop)

/-- `diskPhi` is analytic at every point of the closed unit ball except the
finitely many junction points. -/
lemma analyticAt_diskPhi_of_not_mem_bad (hunit : ∀ k, ‖z₀ k‖ = 1) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (hzB : z ∉ circleBad z₀) :
    AnalyticAt ℂ (diskPhi z₀ r) z := by
  have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  rcases lt_or_eq_of_le hzle with hlt | heq
  · exact Submission.ModelStarDisk.analyticAt_diskPhi z₀ r hunit hlt
  · refine Submission.ModelStarExteriorSep.analyticAt_diskPhi_of (fun k => ?_)
    refine Submission.ModelStarExteriorSep.one_sub_mul_mem_slitPlane (hunit k) heq ?_
    intro hcon
    apply hzB
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
    have hz0 : z₀ k ≠ 0 := junction_ne_zero hunit k
    have hmul : z₀ k * z = 1 := (sub_eq_zero.mp hcon).symm
    have hzeq : z = (z₀ k)⁻¹ := by
      calc z = (z₀ k)⁻¹ * (z₀ k * z) := by
            rw [← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
        _ = (z₀ k)⁻¹ * 1 := by rw [hmul]
        _ = (z₀ k)⁻¹ := mul_one _
    rw [hzeq]

/-- `h_x` is nonzero on the open unit ball, by (P3). -/
lemma hx_ne_zero_of_mem_ball (hs : 0 < s)
    (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {x : ℂ} (hxM : x ∈ modelStarImage z₀ r) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : hx z₀ r x z ≠ 0 := by
  have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  intro hzero
  change diskPhi z₀ r z - x * z = 0 at hzero
  by_cases hz0 : z = 0
  · rw [hz0, diskPhi_zero] at hzero
    simp at hzero
  · have hprod : z * (modelF z₀ r z⁻¹ - x) = 0 := by
      rw [← diskPhi_sub_eq z₀ r hz0]
      exact hzero
    have hFx : modelF z₀ r z⁻¹ = x := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hz0
      · exact sub_eq_zero.mp h
    have hext : z⁻¹ ∈ extSet := by
      rw [extSet]
      show 1 < ‖z⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hzlt
    have hmem : x ∈ modelF z₀ r '' extSet := ⟨z⁻¹, hext, hFx⟩
    have hdisj := Submission.ModelStarExteriorSep.image_ext_inter_image_eq_empty hs hz₀e hunit
      hr hsum hmono hφinj hφlo hφhi
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) x ⟨hmem, hxM⟩

/-- The junction points lie on the unit circle and are not zeros of `h_x`
(for `x ≠ 0`). -/
lemma circleBad_spec (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) {x : ℂ} (hx0 : x ≠ 0) :
    ∀ b ∈ circleBad z₀, b ∈ Metric.sphere (0 : ℂ) 1 ∧ hx z₀ r x b ≠ 0 := by
  intro b hb
  rcases Finset.mem_image.mp hb with ⟨k, -, rfl⟩
  have hz0 : z₀ k ≠ 0 := junction_ne_zero hunit k
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right, norm_inv, hunit k, inv_one]
  · change diskPhi z₀ r (z₀ k)⁻¹ - x * (z₀ k)⁻¹ ≠ 0
    rw [diskPhi_inv_eq_zero hunit hr k]
    simp only [zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hx0 (inv_ne_zero hz0))

/-- **The logarithmic potential of the harmonic measure vanishes off the
origin of the model star** (unconditional: the "Jensen at the boundary"
input is the PROVED commons lemma
`Commons.Analysis.Complex.circleAverage_log_norm_of_analytic_off_finite`). -/
theorem potential_eq_zero_of_mem_of_ne_zero
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {x : ℂ} (hxM : x ∈ modelStarImage z₀ r) (hx0 : x ≠ 0) :
    potential z₀ r x = 0 := by
  have hkey : Real.circleAverage (fun u : ℂ => Real.log ‖hx z₀ r x u‖) 0 1
      = Real.log ‖hx z₀ r x 0‖ := by
    refine Commons.Analysis.Complex.circleAverage_log_norm_of_analytic_off_finite
      (hx z₀ r x) (circleBad z₀) (circleBad_spec hunit hr hx0) ?_ ?_ ?_
    · exact continuousOn_hx hunit hr x
    · intro z hz hzB
      have h1 : AnalyticAt ℂ (diskPhi z₀ r) z :=
        analyticAt_diskPhi_of_not_mem_bad hunit hz hzB
      have h2 : AnalyticAt ℂ (fun u : ℂ => x * u) z := by fun_prop
      change AnalyticAt ℂ (fun u : ℂ => diskPhi z₀ r u - x * u) z
      exact h1.sub h2
    · intro z hz
      exact hx_ne_zero_of_mem_ball hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxM hz
  rw [← circleAverage_log_hx_eq_potential (z₀ := z₀) (r := r) x, hkey]
  change Real.log ‖diskPhi z₀ r 0 - x * 0‖ = 0
  rw [diskPhi_zero]
  norm_num

end Submission.ModelStarPotential
