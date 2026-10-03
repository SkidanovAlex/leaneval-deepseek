import Submission.Lib.Unif2.Work.Analysis.Complex.Hormander.weighted_dbar_adjoint_estimate

/-!
# The weighted Bochner--Kodaira estimate with the curvature hypothesis only on the support

The landed `Work.Analysis.Complex.Hormander.weighted_dbar_adjoint_estimate` requires the pointwise
hypothesis `Δφ ≥ c` *everywhere* on `ℂ`.  For the applications (weights blowing up on the boundary of
a domain, weights built by partition of unity on a surface) only the values on the support of the
test function `u` are ever used: both sides of the inequality are integrals of functions vanishing
off `tsupport u`, and the proof's only use of `Δφ ≥ c` is the comparison
`c * ∫ ‖y‖² ≤ ∫ Δφ ‖y‖²`, which is meaningful only where `‖y‖ ≠ 0`.

Here that comparison is redone with the hypothesis `∀ z ∈ tsupport u, c ≤ Δφ z`, so the estimate
holds for weights that are only controlled on the region where the test function lives.  Everything
else is the proof of `weighted_dbar_adjoint_estimate`, replayed verbatim.
-/

open MeasureTheory
open scoped Topology Pointwise

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.Analysis.Complex.Hormander

open Work.Analysis.Complex.DbarCauchy

/-- **The weighted Bochner--Kodaira estimate with the curvature hypothesis restricted to the
support of the test function.**

For `φ : ℂ → ℝ` of class `C²`, `u : ℂ → ℂ` of class `C¹` with compact support, and `c : ℝ` with
`c ≤ Δφ` on `tsupport u`, one has `c ∫ ‖u‖² e^{-φ} ≤ ∫ ‖∂̄*_φ u‖² e^{-φ}`, where
`∂̄*_φ u = u · dbarBar φ - dbarBar u` is (twice) the formal adjoint of `dbar` for the weighted
measure `e^{-φ}`. -/
theorem weighted_dbar_adjoint_estimate_tsupport {φ : ℂ → ℝ} {u : ℂ → ℂ} {c : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hu : ContDiff ℝ 1 u) (hucs : HasCompactSupport u)
    (hc : ∀ z ∈ tsupport u,
      c ≤ Complex.re (Work.Analysis.Complex.DbarCauchy.dbar
        (Work.Analysis.Complex.DbarCauchy.dbarBar (fun y => (φ y : ℂ))) z)) :
    c * (∫ z : ℂ, ‖u z‖ ^ 2 * Real.exp (-(φ z))) ≤
      ∫ z : ℂ, ‖Work.Analysis.Complex.DbarCauchy.dbarBar u z
          - u z * Work.Analysis.Complex.DbarCauchy.dbarBar (fun y => (φ y : ℂ)) z‖ ^ 2
        * Real.exp (-(φ z)) := by
  set h : ℂ → ℂ := fun z => Complex.exp ((φ z : ℂ) / 2) with hh
  set y : ℂ → ℂ := fun z => u z * Complex.exp (-((φ z : ℂ) / 2)) with hyy
  have hexp1 : ∀ z : ℂ, Complex.exp (-((φ z : ℂ) / 2)) * Complex.exp ((φ z : ℂ) / 2) = 1 := by
    intro z
    rw [← Complex.exp_add]
    have h0 : -((φ z : ℂ) / 2) + (φ z : ℂ) / 2 = 0 := by ring
    rw [h0, Complex.exp_zero]
  have hyu : ∀ z : ℂ, y z * h z = u z := by
    intro z
    rw [hyy, hh, mul_assoc, hexp1 z, mul_one]
  have hyC1 : ContDiff ℝ 1 y := by
    rw [hyy]
    exact hu.mul ((wda_contDiff_exp_negHalf φ hφ).of_le (by norm_num))
  have hycs : HasCompactSupport y := by
    rw [hyy]
    exact hucs.mul_right (f' := fun z => Complex.exp (-((φ z : ℂ) / 2)))
  have hhc : ContDiff ℝ 1 h := by
    rw [hh]
    exact (wda_contDiff_exp_half φ hφ).of_le (by norm_num)
  have hdy : ∀ z : ℂ, DifferentiableAt ℝ y z :=
    fun z => (hyC1.differentiable one_ne_zero).differentiableAt
  have hdh : ∀ z : ℂ, DifferentiableAt ℝ h z :=
    fun z => (hhc.differentiable one_ne_zero).differentiableAt
  have hnorm : ∀ z : ℂ, ‖h z‖ = Real.exp (φ z / 2) := by
    intro z
    rw [hh, Complex.norm_exp]
    simp
  have hdbarh : ∀ z : ℂ, dbarBar h z = h z * (wda_Psi φ z / 2) := by
    intro z
    rw [hh, wda_dbarBar_exp _ _ (((wda_contDiff_half φ hφ).differentiable
      (by norm_num)).differentiableAt)]
    rw [wda_dbarBar_divTwo φ hφ z]
  have hsub : ∀ z : ℂ, dbarBar u z - u z * wda_Psi φ z
      = h z * (dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z) := by
    intro z
    have hdu : dbarBar (fun z' => y z' * h z') z = dbarBar u z := by
      rw [show (fun z' => y z' * h z') = u from funext hyu]
    rw [← hdu, dbarBar_mul _ _ z (hdy z) (hdh z), hdbarh z, ← hyu z]
    push_cast
    ring
  have hnormu : ∀ z : ℂ, ‖dbarBar u z - u z * wda_Psi φ z‖ ^ 2 * Real.exp (-(φ z))
      = ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 := by
    intro z
    rw [hsub z, norm_mul, mul_pow, hnorm z, wda_exp_half_sq]
    exact wda_exp_sandwich_right (φ z) _
  have hnormy : ∀ z : ℂ, ‖u z‖ ^ 2 * Real.exp (-(φ z)) = ‖y z‖ ^ 2 := by
    intro z
    rw [← hyu z, norm_mul, mul_pow, hnorm z, wda_exp_half_sq]
    exact wda_exp_sandwich_left (φ z) _
  rw [show (fun z : ℂ => ‖u z‖ ^ 2 * Real.exp (-(φ z))) = fun z => ‖y z‖ ^ 2 from funext hnormy]
  rw [show (fun z : ℂ => ‖dbarBar u z - u z * dbarBar (fun y => (φ y : ℂ)) z‖ ^ 2
        * Real.exp (-(φ z)))
      = fun z => ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2
      from funext hnormu]
  have hNcont : Continuous fun z : ℂ => ‖y z‖ ^ 2 := hyC1.continuous.norm.pow 2
  have hNcs : HasCompactSupport fun z : ℂ => ‖y z‖ ^ 2 :=
    hycs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hI1 : Integrable (fun z : ℂ => wda_lap φ z * ‖y z‖ ^ 2) volume := by
    refine ((wda_continuous_lap φ hφ).mul hNcont).integrable_of_hasCompactSupport ?_
    exact hNcs.mul_left (f := wda_lap φ)
  have hI2 : Integrable (fun z : ℂ => c * ‖y z‖ ^ 2) volume := by
    refine (continuous_const.mul hNcont).integrable_of_hasCompactSupport ?_
    exact hNcs.mul_left (f := fun _ : ℂ => c)
  have hlap : c * (∫ z : ℂ, ‖y z‖ ^ 2 ∂volume) ≤ ∫ z : ℂ, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := by
    rw [← integral_const_mul]
    refine integral_mono hI2 hI1 (fun z => ?_)
    by_cases hz : y z = 0
    · rw [hz]
      simp
    · have huz : u z ≠ 0 := by
        intro h0
        exact hz (by rw [hyy]; simp [h0])
      have hmem : z ∈ tsupport u := subset_tsupport u (Function.mem_support.mpr huz)
      have hcz : c ≤ wda_lap φ z := by
        have := hc z hmem
        simpa only [wda_lap, wda_Psi] using this
      exact mul_le_mul_of_nonneg_right hcz (by positivity)
  have hE := wda_bochner_kodaira_c1 φ y hφ hyC1 hycs
  calc c * (∫ z : ℂ, ‖y z‖ ^ 2 ∂volume) ≤ ∫ z : ℂ, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := hlap
    _ ≤ ∫ z : ℂ, ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 ∂volume := by
        rw [hE]
        have h0 : 0 ≤ ∫ z : ℂ,
            ‖dbar y z + ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z‖ ^ 2 ∂volume :=
          integral_nonneg (fun z => by positivity)
        linarith

end Work.Analysis.Complex.Hormander
