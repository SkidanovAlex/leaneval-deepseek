import Mathlib
import Submission.Commons.Analysis.Complex.sphere_mirror_log
import Submission.Commons.Analysis.Complex.zeroFactor_g

noncomputable section

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped BigOperators Topology

namespace Commons.Analysis.Complex

/-- The logarithm of the norm of the factorized-rational product `∏ᶠ u (z-u)^{d u}`
(where `d` is supported exactly on the finset `S`, and `z` avoids `S`) equals
the sum `∑ u ∈ S, d u · log ‖z-u‖`. -/
lemma log_norm_finprod_zpow_boundary {z : ℂ} {S : Finset ℂ} {d : ℂ → ℤ}
    (hSmem : ∀ u, u ∈ S ↔ d u ≠ 0) (hzS : ∀ u ∈ S, z ≠ u) :
    Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ =
      ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖z - u‖ := by
  classical
  have hprod : (∏ᶠ u : ℂ, (z - u) ^ d u) = ∏ u ∈ S, (z - u) ^ d u := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    have hd : d u ≠ 0 := by
      intro h0
      exact hu (by simp [h0])
    exact (hSmem u).2 hd
  rw [hprod]
  have hne : ∀ x ∈ S, ‖(z - x) ^ d x‖ ≠ 0 := by
    intro x hx
    have hzx : (z - x) ≠ 0 := sub_ne_zero.mpr (hzS x hx)
    exact norm_ne_zero_iff.mpr (zpow_ne_zero (d x) hzx)
  rw [Complex.norm_prod, Real.log_prod hne]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Complex.norm_zpow, Real.log_zpow]

/-- For an analytic function, the divisor vanishes at points where the function does not. -/
lemma divisor_eq_zero_of_analytic_ne_zero {a u : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a R)) (hu : u ∈ Metric.closedBall a R)
    (hfu : f u ≠ 0) : (MeromorphicOn.divisor f (Metric.closedBall a R)) u = 0 := by
  have hord : meromorphicOrderAt f u = 0 :=
    meromorphicOrderAt_eq_zero_of_ne_zero (hf u hu) hfu
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, hord]
  simp

theorem log_boundary_factor {a : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ} {z : ℂ}
    (hfac : ∀ z ∈ Metric.closedBall a R,
        f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ)) * g z)
    (hgf : ∀ z ∈ Metric.closedBall a R, g z ≠ 0)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|))
    (hfa : f a ≠ 0)
    (hsphere : ∀ u, ‖u - a‖ = R → f u ≠ 0)
    {S : Finset ℂ}
    (hS_mem : ∀ u, u ∈ S ↔ (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u ≠ 0)
    (hz : ‖z - a‖ = R) :
    Real.log ‖f z‖ =
      Real.log ‖g z‖ +
        ∑ u ∈ S, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
          (Real.log ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ +
            Real.log (‖u - a‖ / R)) := by
  classical
  rw [abs_of_pos hR] at hfac hf hS_mem ⊢
  let d : ℂ → ℤ := fun u => (MeromorphicOn.divisor f (Metric.closedBall a R)) u
  have hzCB : z ∈ Metric.closedBall a R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_eq hz
  have hfz0 : f z ≠ 0 := hsphere z hz
  have hgz0 : g z ≠ 0 := hgf z hzCB
  have hfac_z : f z = (∏ᶠ u : ℂ, (z - u) ^ (d u)) * g z := by
    simpa [d] using hfac z hzCB
  have hS_mem_d : ∀ u, u ∈ S ↔ d u ≠ 0 := by
    intro u
    simpa [d] using hS_mem u
  have hd_mem_CB : ∀ u, u ∈ S → u ∈ Metric.closedBall a R := by
    intro u hu
    have hdu : d u ≠ 0 := (hS_mem_d u).1 hu
    have hsup : u ∈ Function.support (MeromorphicOn.divisor f (Metric.closedBall a R)) := by
      rw [Function.mem_support]
      simpa [d] using hdu
    exact Function.locallyFinsuppWithin.supportWithinDomain
      (MeromorphicOn.divisor f (Metric.closedBall a R)) hsup
  have hfu0 : ∀ u, u ∈ S → f u = 0 := by
    intro u hu
    by_contra hfu
    have hdu : d u ≠ 0 := (hS_mem_d u).1 hu
    exact hdu (by simpa [d] using divisor_eq_zero_of_analytic_ne_zero hf (hd_mem_CB u hu) hfu)
  have hu_ne_a : ∀ u, u ∈ S → u ≠ a := by
    intro u hu hua
    have : f a = 0 := by simpa [hua] using hfu0 u hu
    exact hfa this
  have hz_notS : z ∉ S := by
    intro hzS
    have hd : d z ≠ 0 := (hS_mem_d z).1 hzS
    exact hd (by simpa [d] using divisor_eq_zero_of_analytic_ne_zero hf hzCB hfz0)
  have hz_ne_u : ∀ u, u ∈ S → z ≠ u := by
    intro u hu hzu
    exact hz_notS (by simpa [hzu] using hu)
  have hP0 : (∏ᶠ u : ℂ, (z - u) ^ d u) ≠ 0 := by
    intro hP
    have hfz_eq : f z = 0 := by
      rw [hfac_z, hP]
      simp
    exact hfz0 hfz_eq
  have hprodlog : Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ =
      ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖z - u‖ := by
    exact log_norm_finprod_zpow_boundary hS_mem_d hz_ne_u
  have hsum : (∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖z - u‖) =
      ∑ u ∈ S, ((d u : ℤ) : ℝ) *
        (Real.log ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ +
          Real.log (‖u - a‖ / R)) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hlog := sphere_mirror_log hR hz (hu_ne_a u hu) (hz_ne_u u hu)
    rw [hlog]
  calc
    Real.log ‖f z‖
        = Real.log ‖g z‖ + Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ := by
            have hfzn : ‖f z‖ ≠ 0 := norm_ne_zero_iff.mpr hfz0
            have hgzn : ‖g z‖ ≠ 0 := norm_ne_zero_iff.mpr hgz0
            have hPn : ‖∏ᶠ u : ℂ, (z - u) ^ d u‖ ≠ 0 := norm_ne_zero_iff.mpr hP0
            calc
              Real.log ‖f z‖ = Real.log ‖(∏ᶠ u : ℂ, (z - u) ^ d u) * g z‖ := by
                  rw [hfac_z]
              _ = Real.log (‖∏ᶠ u : ℂ, (z - u) ^ d u‖ * ‖g z‖) := by
                  rw [norm_mul]
              _ = Real.log ‖∏ᶠ u : ℂ, (z - u) ^ d u‖ + Real.log ‖g z‖ := by
                  exact Real.log_mul hPn hgzn
              _ = Real.log ‖g z‖ + Real.log ‖∏ᶠ u : ℂ, (z - u) ^ d u‖ := by
                  ring
    _ = Real.log ‖g z‖ + ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖z - u‖ := by
          rw [hprodlog]
    _ = Real.log ‖g z‖ + ∑ u ∈ S, ((d u : ℤ) : ℝ) *
          (Real.log ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ +
            Real.log (‖u - a‖ / R)) := by
          rw [hsum]

end Commons.Analysis.Complex
