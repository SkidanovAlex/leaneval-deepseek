/-
⚠ IMPORT-CLASH WORKAROUND (session 118).

The commons currently contains TWO different modules that both declare the constant
`Commons.Analysis.GaussianMeasure.toLp_norm_sq`:
  * `Submission.Commons.Analysis.GaussianMeasure.bobkov_strong_nD` (~line 153), and
  * `Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated` (~line 2537).
Lean refuses to load both in one environment ("environment already contains ..."), so any
module whose import closure contains both fails to build.  The theorem path needs
`bobkov_strong_nD` (through `Concentration` -> `gaussian_isoperimetric_blowup`) and, for the
CFM04 (B)-conjecture, `brascamp_lieb_truncated`.

This file is a verbatim copy of
`Submission.Commons.Analysis.GaussianMeasure.B_conjecture_diagonal`
with the *unused* line `import Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated`
deleted, so that `Submission.IsotropicMass` can use
`Commons.Analysis.GaussianMeasure.B_conjecture_diagonal` without pulling in the clashing
module.  (The import is genuinely unused: this copy compiles with it removed.)

PROPER FIX (for whoever can write into the commons): delete or rename the duplicate
`toLp_norm_sq` in one of those two commons modules; then this file can be deleted and
`Submission/IsotropicMass.lean` can import the commons module again.

⚠ Until then: NEVER import both this module and
`Submission.Commons.Analysis.GaussianMeasure.B_conjecture_diagonal` -- they declare the same
constants.

The content below is copied verbatim from the commons module.
-/
import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.B_conj_of_even_poincare
import Submission.Commons.Analysis.InnerProductSpace.combination_close_of_orthogonal_const
import Submission.Commons.Analysis.InnerProductSpace.integral_symmPart_sq_le
import Submission.Commons.Analysis.GaussianMeasure.laplacian_weighted_comp_neg
import Submission.Commons.Analysis.GaussianMeasure.laplacian_weighted_linear
import Submission.Commons.Analysis.GaussianMeasure.memLp_weightedLaplacian_c2
import Submission.Commons.Analysis.GaussianMeasure.isFiniteMeasure_withDensity_exp_neg
import Submission.Commons.Analysis.GaussianMeasure.memLp_withDensity_exp_neg
import Submission.Commons.Analysis.GaussianMeasure.even_poincare_truncated_of_smooth
import Submission.Commons.Analysis.GaussianMeasure.even_poincare_smooth_of_density_mean
import Submission.Commons.Analysis.GaussianMeasure.creation_energy_bound_even
import Submission.Commons.Topology.Support.hasCompactSupport_finset_sum
import Submission.Commons.Analysis.GaussianMeasure.weighted_energy_identity_moll_measurable
import Submission.Commons.Analysis.GaussianMeasure.ae_const_of_forall_deriv_integral_zero
import Submission.Commons.Analysis.GaussianMeasure.integrableOn_sq_of_integrable_sq_mul_exp_neg
import Submission.Commons.Analysis.Measure.locallyIntegrable_of_aestronglyMeasurable_of_integrableOn_sq
import Submission.Commons.Analysis.GaussianMeasure.weak_solution_const_of_weakGradient_transfer
import Submission.Commons.Analysis.GaussianMeasure.l2_cauchy_schwarz_grad
import Submission.Commons.Analysis.MeasureTheory.lintegral_ofReal_le_of_tendsto_of_nonneg
import Submission.Commons.Analysis.Sobolev.weakGradient_of_memSobolev_one
import Submission.Commons.Analysis.Sobolev.memSobolev_one_of_weak_solutionH1
import Submission.Commons.Analysis.Elliptic.memLp_psi_and_grad
import Submission.Commons.Analysis.Schwartz.eq_zero_of_forall_hasCompactSupport
import Submission.Commons.Analysis.GaussianMeasure.convex_sub_quadratic_lower_bound

open MeasureTheory
open scoped ENNReal ContDiff Topology

namespace Commons.Analysis.GaussianMeasure

namespace BCD

section Weyl
open _root_.MeasureTheory _root_.Filter
open scoped ENNReal ContDiff Topology
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

open Filter

noncomputable def cut (χ : ContDiffBump (0 : E)) (R : ℝ) : E → ℝ :=
  fun x => (χ : E → ℝ) (R⁻¹ • x)

lemma cut_contDiff (χ : ContDiffBump (0 : E)) (R : ℝ) (m : ℕ∞) : ContDiff ℝ m (cut χ R) :=
  χ.contDiff.comp (contDiff_id.const_smul (R⁻¹))

lemma cut_nonneg (χ : ContDiffBump (0 : E)) (R : ℝ) (x : E) : 0 ≤ cut χ R x := χ.nonneg
lemma cut_le_one (χ : ContDiffBump (0 : E)) (R : ℝ) (x : E) : cut χ R x ≤ 1 := χ.le_one

lemma cut_hasCompactSupport (χ : ContDiffBump (0 : E)) (R : ℝ) (hR : R ≠ 0) :
    HasCompactSupport (cut χ R) := by
  have h := χ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (by simpa using hR))
  show HasCompactSupport (fun x => (χ : E → ℝ) (R⁻¹ • x))
  exact h

lemma cut_zero (χ : ContDiffBump (0 : E)) : (χ : E → ℝ) 0 = 1 :=
  χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact χ.rIn_pos.le)

lemma cut_tendsto (χ : ContDiffBump (0 : E)) (x : E) :
    Tendsto (fun R : ℝ => cut χ R x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun R : ℝ => R⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) := h1.smul_const x
  rw [zero_smul] at h2
  have h3 : Tendsto (fun R : ℝ => (χ : E → ℝ) (R⁻¹ • x)) atTop (𝓝 ((χ : E → ℝ) 0)) :=
    (χ.continuous.tendsto 0).comp h2
  rw [cut_zero] at h3
  simpa [cut] using h3

lemma exists_cut_fderiv_bound (χ : ContDiffBump (0 : E)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ y : E, ‖fderiv ℝ (χ : E → ℝ) y‖ ≤ Λ := by
  have hcont : Continuous (fun y : E => fderiv ℝ (χ : E → ℝ) y) :=
    (χ.contDiff (n := ⊤)).continuous_fderiv (by simp)
  obtain ⟨Λ, hΛ⟩ := hcont.bounded_above_of_compact_support (χ.hasCompactSupport.fderiv ℝ)
  exact ⟨max Λ 0, le_max_right _ _, fun y => le_trans (hΛ y) (le_max_left _ _)⟩

lemma cut_fderiv_bound (χ : ContDiffBump (0 : E)) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y : E, ‖fderiv ℝ (χ : E → ℝ) y‖ ≤ Λ)
    (R : ℝ) (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (cut χ R) x‖ ≤ Λ * R⁻¹ := by
  have hL : HasFDerivAt (fun x : E => R⁻¹ • x) (R⁻¹ • (1 : E →L[ℝ] E)) x :=
    ContinuousLinearMap.hasFDerivAt (R⁻¹ • (1 : E →L[ℝ] E)) (x := x)
  have hr : HasFDerivAt (χ : E → ℝ) (fderiv ℝ (χ : E → ℝ) (R⁻¹ • x)) (R⁻¹ • x) :=
    ((χ.contDiff (n := ⊤)).contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hc : fderiv ℝ (cut χ R) x
      = (fderiv ℝ (χ : E → ℝ) (R⁻¹ • x)).comp (R⁻¹ • (1 : E →L[ℝ] E)) :=
    (hr.comp x hL).fderiv
  rw [hc]
  calc ‖(fderiv ℝ (χ : E → ℝ) (R⁻¹ • x)).comp (R⁻¹ • (1 : E →L[ℝ] E))‖
      ≤ ‖fderiv ℝ (χ : E → ℝ) (R⁻¹ • x)‖ * ‖R⁻¹ • (1 : E →L[ℝ] E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Λ * R⁻¹ := by
        have hnorm : ‖(R⁻¹ : ℝ) • (1 : E →L[ℝ] E)‖ ≤ R⁻¹ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
          calc R⁻¹ * ‖(1 : E →L[ℝ] E)‖ ≤ R⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.mpr hR.le)
            _ = R⁻¹ := by ring
        exact mul_le_mul (hΛ _) hnorm (norm_nonneg _) hΛ0

lemma cut_eq_one_of_norm_le (χ : ContDiffBump (0 : E)) (hχ : χ.rIn = 1) {R : ℝ} (hR : 0 < R)
    {x : E} (hx : ‖x‖ ≤ R) : cut χ R x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hχ, inv_mul_le_one₀ hR]
  exact hx

theorem weighted_energy_cutoff_zero_aux
    (f g : E → ℝ) (G : E → E)
    (hf : Continuous f) (hGmeas : AEStronglyMeasurable G volume)
    (hg2 : Integrable (fun x => g x ^ 2 * Real.exp (-(f x))) volume)
    (hGloc : ∀ K : Set E, IsCompact K → IntegrableOn (fun x => ‖G x‖ ^ 2) K volume)
    (henergy : ∀ η : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∫ x, η x ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
        = -2 * ∫ x, η x * g x * (fderiv ℝ η x) (G x) * Real.exp (-(f x))) :
    ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(f x))) = 0 := by
  classical
  set χ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩ with hχdef
  have hχrIn : χ.rIn = 1 := by rw [hχdef]
  obtain ⟨Λ, hΛ0, hΛb⟩ := exists_cut_fderiv_bound χ
  have hΛ : ∀ R : ℝ, 0 < R → ∀ x : E, ‖fderiv ℝ (cut χ R) x‖ ≤ Λ * R⁻¹ :=
    fun R hR x => cut_fderiv_bound χ Λ hΛ0 hΛb R hR x
  set B : ℝ := ∫ x, g x ^ 2 * Real.exp (-(f x)) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hGli : LocallyIntegrable (fun x : E => ‖G x‖ ^ 2) volume :=
    locallyIntegrable_iff.mpr hGloc
  have hgl2 : LocallyIntegrable (fun x : E => g x ^ 2) volume :=
    locallyIntegrable_iff.mpr fun K hK => integrableOn_sq_of_integrable_sq_mul_exp_neg f g hf hg2 K hK
  have hgabs : AEStronglyMeasurable (fun x : E => |g x|) volume := by
    have h1 : AEStronglyMeasurable (fun x : E => g x ^ 2) volume := hgl2.aestronglyMeasurable
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable h1).congr
      (Eventually.of_forall fun x => ?_)
    show Real.sqrt (g x ^ 2) = |g x|
    rw [Real.sqrt_sq_eq_abs]
  -- (1) integrability of the cutoff energy
  have hcutint : ∀ R : ℝ, 0 < R →
      Integrable (fun x : E => (cut χ R x) ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))) volume := by
    intro R hR
    have hcont : Continuous (fun x : E => (cut χ R x) ^ 2 * Real.exp (-(f x))) :=
      (((cut_contDiff χ R ⊤).continuous).pow 2).mul (Real.continuous_exp.comp hf.neg)
    have hcs : HasCompactSupport (fun x : E => (cut χ R x) ^ 2 * Real.exp (-(f x))) := by
      refine (cut_hasCompactSupport χ R (ne_of_gt hR)).mono' fun x hx => ?_
      have hx' : (cut χ R x) ^ 2 * Real.exp (-(f x)) ≠ 0 := hx
      exact subset_closure (Function.mem_support.mpr fun h0 => hx' (by rw [h0]; ring))
    have h := hGli.integrable_smul_left_of_hasCompactSupport hcont hcs
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  -- (2) integrability of the cross term
  have hcrossint : ∀ R : ℝ, 0 < R →
      Integrable (fun x : E => cut χ R x * |g x| * ‖G x‖ * Real.exp (-(f x))) volume := by
    intro R hR
    have hcont1 : Continuous (fun x : E => cut χ R x * Real.exp (-(f x))) :=
      (cut_contDiff χ R ⊤).continuous.mul (Real.continuous_exp.comp hf.neg)
    have hcs1 : HasCompactSupport (fun x : E => cut χ R x * Real.exp (-(f x))) :=
      (cut_hasCompactSupport χ R (ne_of_gt hR)).mul_right (f' := fun x : E => Real.exp (-(f x)))
    have hA : Integrable (fun x : E => cut χ R x * Real.exp (-(f x)) * g x ^ 2) volume :=
      hgl2.integrable_smul_left_of_hasCompactSupport hcont1 hcs1
    have hB' : Integrable (fun x : E => cut χ R x * Real.exp (-(f x)) * ‖G x‖ ^ 2) volume :=
      hGli.integrable_smul_left_of_hasCompactSupport hcont1 hcs1
    have hdom : Integrable (fun x : E => ((cut χ R x * Real.exp (-(f x)) * g x ^ 2)
        + (cut χ R x * Real.exp (-(f x)) * ‖G x‖ ^ 2)) / 2) volume := (hA.add hB').div_const 2
    refine hdom.mono' ?_ ?_
    · exact (((((cut_contDiff χ R ⊤).continuous.aestronglyMeasurable).mul hgabs).mul
        hGmeas.norm).mul (Real.continuous_exp.comp hf.neg).aestronglyMeasurable)
    · filter_upwards with x
      have h1 : 0 ≤ cut χ R x := cut_nonneg χ R x
      have h2 : 0 ≤ Real.exp (-(f x)) := (Real.exp_pos _).le
      have h3 : 0 ≤ ‖G x‖ := norm_nonneg _
      have h4 : 2 * |g x| * ‖G x‖ ≤ g x ^ 2 + ‖G x‖ ^ 2 := by
        nlinarith [sq_nonneg (|g x| - ‖G x‖), sq_abs (g x), abs_nonneg (g x)]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg h1,
        abs_of_nonneg (abs_nonneg (g x)), abs_of_nonneg h3, abs_of_nonneg h2]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have h5 : 0 ≤ cut χ R x * Real.exp (-(f x)) := mul_nonneg h1 h2
      have h6 := mul_le_mul_of_nonneg_left h4 h5
      nlinarith [h6]
  -- (3) the Caccioppoli bound
  have hbound : ∀ R : ℝ, 0 < R → ∫ x, (cut χ R x) ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
      ≤ 4 * Λ ^ 2 * B / R ^ 2 := by
    intro R hR
    have hAint := hcutint R hR
    set A : ℝ := ∫ x, (cut χ R x) ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x)) with hAdef
    have hAnn : 0 ≤ A := by
      rw [hAdef]
      refine integral_nonneg fun x => ?_
      have h1 := cut_nonneg χ R x
      positivity
    -- Cauchy-Schwarz
    have hAI : Integrable (fun x : E => (cut χ R x * ‖G x‖) ^ 2 * Real.exp (-(f x))) volume := by
      refine hAint.congr (Eventually.of_forall fun x => ?_)
      show cut χ R x ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
        = (cut χ R x * ‖G x‖) ^ 2 * Real.exp (-(f x))
      ring
    have hBI : Integrable (fun x : E => |g x| ^ 2 * Real.exp (-(f x))) volume := by
      refine hg2.congr (Eventually.of_forall fun x => ?_)
      show g x ^ 2 * Real.exp (-(f x)) = |g x| ^ 2 * Real.exp (-(f x))
      rw [sq_abs]
    have ha : 0 ≤ fun x : E => cut χ R x * ‖G x‖ := fun x =>
      mul_nonneg (cut_nonneg χ R x) (norm_nonneg _)
    have hb : 0 ≤ fun x : E => |g x| := fun x => abs_nonneg _
    have hw : 0 ≤ fun x : E => Real.exp (-(f x)) := fun x => (Real.exp_pos _).le
    have hameas : AEMeasurable (fun x : E => cut χ R x * ‖G x‖) volume :=
      ((((cut_contDiff χ R ⊤).continuous.aestronglyMeasurable).mul hGmeas.norm)).aemeasurable
    have hbmeas : AEMeasurable (fun x : E => |g x|) volume := hgabs.aemeasurable
    have hwmeas : AEMeasurable (fun x : E => Real.exp (-(f x))) volume :=
      (Real.continuous_exp.comp hf.neg).aemeasurable
    have hBI : Integrable (fun x : E => |g x| ^ 2 * Real.exp (-(f x))) volume := by
      refine hg2.congr (Eventually.of_forall fun x => ?_)
      show g x ^ 2 * Real.exp (-(f x)) = |g x| ^ 2 * Real.exp (-(f x))
      rw [sq_abs]
    have hCS := weighted_cauchy_schwarz (volume : Measure E) (fun x : E => cut χ R x * ‖G x‖)
      (fun x : E => |g x|) (fun x : E => Real.exp (-(f x))) hw ha hb hameas hbmeas hwmeas
      (by
        refine hAint.congr (Eventually.of_forall fun x => ?_)
        show cut χ R x ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
          = (cut χ R x * ‖G x‖) ^ 2 * Real.exp (-(f x))
        ring) hBI
    have hCS' : (∫ x, cut χ R x * |g x| * ‖G x‖ * Real.exp (-(f x))) ≤ Real.sqrt A * Real.sqrt B := by
      have h1 : (∫ x, cut χ R x * ‖G x‖ * |g x| * Real.exp (-(f x)))
          = ∫ x, cut χ R x * |g x| * ‖G x‖ * Real.exp (-(f x)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => by ring)
      have h2 : (∫ x, (cut χ R x * ‖G x‖) ^ 2 * Real.exp (-(f x))) = A := by
        rw [hAdef]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show (cut χ R x * ‖G x‖) ^ 2 * Real.exp (-(f x))
          = cut χ R x ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
        ring
      have h3 : (∫ x, |g x| ^ 2 * Real.exp (-(f x))) = B := by
        rw [hBdef]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show |g x| ^ 2 * Real.exp (-(f x)) = g x ^ 2 * Real.exp (-(f x))
        rw [sq_abs]
      rw [h1, h2, h3] at hCS
      exact hCS
    set I : ℝ := ∫ x, cut χ R x * g x * (fderiv ℝ (cut χ R) x) (G x) * Real.exp (-(f x)) with hIdef
    have hTle : |I| ≤ Λ * R⁻¹ * (∫ x, cut χ R x * |g x| * ‖G x‖ * Real.exp (-(f x))) := by
      have hpt : ∀ x : E, |cut χ R x * g x * (fderiv ℝ (cut χ R) x) (G x) * Real.exp (-(f x))|
          ≤ Λ * R⁻¹ * (cut χ R x * |g x| * ‖G x‖ * Real.exp (-(f x))) := by
        intro x
        have h1 : 0 ≤ cut χ R x := cut_nonneg χ R x
        have h2 : 0 ≤ Real.exp (-(f x)) := (Real.exp_pos _).le
        have h4 : 0 ≤ Λ * R⁻¹ := mul_nonneg hΛ0 (inv_nonneg.mpr hR.le)
        have h3 : ‖(fderiv ℝ (cut χ R) x) (G x)‖ ≤ Λ * R⁻¹ * ‖G x‖ := by
          calc ‖(fderiv ℝ (cut χ R) x) (G x)‖ ≤ ‖fderiv ℝ (cut χ R) x‖ * ‖G x‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ Λ * R⁻¹ * ‖G x‖ := by
                gcongr
                exact hΛ R hR x
        have h3' : |(fderiv ℝ (cut χ R) x) (G x)| ≤ Λ * R⁻¹ * ‖G x‖ := by
          rwa [Real.norm_eq_abs] at h3
        have hgn : 0 ≤ |g x| := abs_nonneg _
        have hGn : 0 ≤ ‖G x‖ := norm_nonneg _
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
        have h5 : 0 ≤ cut χ R x * |g x| * Real.exp (-(f x)) :=
          mul_nonneg (mul_nonneg h1 hgn) h2
        have h6 := mul_le_mul_of_nonneg_left h3' h5
        nlinarith [h6, h4]
      rw [hIdef]
      refine le_trans abs_integral_le_integral_abs ?_
      rw [← integral_const_mul]
      exact integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
        ((hcrossint R hR).const_mul _) (Eventually.of_forall hpt)
    have hE := henergy (cut χ R) (cut_contDiff χ R ⊤) (cut_hasCompactSupport χ R (ne_of_gt hR))
    have hEq : A = -2 * I := by
      rw [hAdef, hIdef]
      exact hE
    have h2 : |I| ≤ Λ * R⁻¹ * (Real.sqrt A * Real.sqrt B) :=
      le_trans hTle (mul_le_mul_of_nonneg_left hCS' (mul_nonneg hΛ0 (inv_nonneg.mpr hR.le)))
    have hAle : A ≤ 2 * (Λ * R⁻¹) * Real.sqrt A * Real.sqrt B := by
      have h3 : |(-2 : ℝ) * I| ≤ 2 * (Λ * R⁻¹) * Real.sqrt A * Real.sqrt B := by
        have h5 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 2)
        rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        calc 2 * |I| ≤ 2 * (Λ * R⁻¹ * (Real.sqrt A * Real.sqrt B)) := h5
          _ = 2 * (Λ * R⁻¹) * Real.sqrt A * Real.sqrt B := by ring
      calc A = -2 * I := hEq
        _ ≤ |(-2 : ℝ) * I| := le_abs_self _
        _ ≤ 2 * (Λ * R⁻¹) * Real.sqrt A * Real.sqrt B := h3
    have hA2 : A ≤ (2 * (Λ * R⁻¹) * Real.sqrt B) ^ 2 := by
      have hfac : Real.sqrt A * (Real.sqrt A - 2 * (Λ * R⁻¹) * Real.sqrt B) ≤ 0 := by
        nlinarith [hAle, Real.sq_sqrt hAnn]
      rcases eq_or_lt_of_le (Real.sqrt_nonneg A) with h | h
      · have hA0 : A = 0 := by nlinarith [Real.sq_sqrt hAnn]
        rw [hA0]
        positivity
      · have hle : Real.sqrt A ≤ 2 * (Λ * R⁻¹) * Real.sqrt B := by nlinarith [hfac]
        calc A = (Real.sqrt A) ^ 2 := (Real.sq_sqrt hAnn).symm
          _ ≤ (2 * (Λ * R⁻¹) * Real.sqrt B) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg A) hle 2
    have hsq : (2 * (Λ * R⁻¹) * Real.sqrt B) ^ 2 = 4 * Λ ^ 2 * B / R ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hBnn, inv_pow]
      field_simp
      ring
    rw [hsq] at hA2
    exact hA2
  -- (4) the weighted energy on each ball vanishes
  have hballzero : ∀ r : ℝ, 0 < r →
      ∫ x in Metric.closedBall (0 : E) r, ‖G x‖ ^ 2 * Real.exp (-(f x)) = 0 := by
    intro r hr
    have hSnn : 0 ≤ ∫ x in Metric.closedBall (0 : E) r, ‖G x‖ ^ 2 * Real.exp (-(f x)) :=
      integral_nonneg fun x => by positivity
    refine le_antisymm ?_ hSnn
    have htend : Tendsto (fun m : ℕ => 4 * Λ ^ 2 * B / (r + (m : ℝ)) ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m : ℕ => (r + (m : ℝ))) atTop atTop :=
        tendsto_atTop_add_const_left atTop r tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun m : ℕ => (r + (m : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp h0
      have h2 : Tendsto (fun m : ℕ => 4 * Λ ^ 2 * B * ((r + (m : ℝ))⁻¹) ^ 2)
          atTop (𝓝 (4 * Λ ^ 2 * B * (0:ℝ) ^ 2)) := tendsto_const_nhds.mul (h1.pow 2)
      simpa [div_eq_mul_inv, inv_pow] using h2
    refine le_of_tendsto_of_tendsto tendsto_const_nhds htend (Eventually.of_forall fun m => ?_)
    have hm : 0 < r + (m : ℝ) := by positivity
    have hSle : ∫ x in Metric.closedBall (0 : E) r, ‖G x‖ ^ 2 * Real.exp (-(f x))
        ≤ ∫ x, (cut χ (r + m) x) ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x)) := by
      have hone : ∀ x ∈ Metric.closedBall (0 : E) r, cut χ (r + m) x = 1 := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        exact cut_eq_one_of_norm_le χ hχrIn hm (le_trans hx (le_add_of_nonneg_right (Nat.cast_nonneg m)))
      rw [← integral_indicator (Metric.isClosed_closedBall.measurableSet)]
      refine integral_mono_of_nonneg ?_ (hcutint _ hm) (Eventually.of_forall fun x => ?_)
      · refine Eventually.of_forall fun x => ?_
        by_cases hx : x ∈ Metric.closedBall (0 : E) r
        · rw [Set.indicator_of_mem hx]
          positivity
        · rw [Set.indicator_of_notMem hx]
          exact le_refl 0
      · by_cases hx : x ∈ Metric.closedBall (0 : E) r
        · rw [Set.indicator_of_mem hx]
          show ‖G x‖ ^ 2 * Real.exp (-(f x))
            ≤ (cut χ (r + m) x) ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
          rw [hone x hx, one_pow, one_mul]
        · rw [Set.indicator_of_notMem hx]
          positivity
    exact le_trans hSle (hbound _ hm)
  -- (5) conclude via monotone convergence
  set s : ℕ → Set E := fun m => Metric.closedBall (0 : E) ((m : ℝ) + 1) with hs
  have hsm : ∀ m, MeasurableSet (s m) := fun m => Metric.isClosed_closedBall.measurableSet
  have hsmem : ∀ m, ∫ x in s m, ‖G x‖ ^ 2 * Real.exp (-(f x)) = 0 := fun m =>
    hballzero ((m : ℝ) + 1) (by positivity)
  have hpoint : ∀ x : E, (⨆ m, (s m).indicator (fun y : E =>
      ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) x)
      = ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(f x))) := by
    intro x
    refine le_antisymm (iSup_le fun m => ?_) ?_
    · by_cases hx : x ∈ s m
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    obtain ⟨m, hm⟩ : ∃ m : ℕ, x ∈ s m := by
      refine ⟨⌈‖x‖⌉₊, ?_⟩
      rw [hs, Metric.mem_closedBall, dist_zero_right]
      push_cast
      exact le_trans (Nat.le_ceil ‖x‖) (le_add_of_nonneg_right (by norm_num))
    exact le_iSup_of_le m (by rw [Set.indicator_of_mem hm])
  have hmono : ∀ᵐ x ∂(volume : Measure E), Monotone (fun m : ℕ => (s m).indicator
      (fun y : E => ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) x) := by
    refine Eventually.of_forall fun x => ?_
    intro m l hml
    show (s m).indicator (fun y : E => ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) x
      ≤ (s l).indicator (fun y : E => ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) x
    by_cases hx : x ∈ s m
    · have hxl : x ∈ s l := by
        refine Metric.closedBall_subset_closedBall ?_ hx
        exact_mod_cast Nat.succ_le_succ hml
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxl]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have haesm : ∀ m, AEMeasurable ((s m).indicator (fun y : E =>
      ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) : E → ℝ≥0∞) volume := by
    intro m
    refine AEMeasurable.indicator ?_ (hsm m)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aestronglyMeasurable_iff_aemeasurable.mp
      ((hGmeas.norm.pow 2).mul (Real.continuous_exp.comp hf.neg).aestronglyMeasurable))
  have hMCT := lintegral_iSup' haesm hmono
  have hterm : ∀ m, ∫⁻ x, (s m).indicator (fun y : E =>
      ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) x ∂(volume : Measure E) = 0 := by
    intro m
    rw [lintegral_indicator (hsm m)]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [hsmem m, ENNReal.ofReal_zero]
    · have hK : IsCompact (s m) := by
        rw [hs]
        show IsCompact (Metric.closedBall (0 : E) ((m:ℝ) + 1))
        exact isCompact_closedBall 0 _
      have hGi : Integrable (fun x : E => ‖G x‖ ^ 2) (volume.restrict (s m)) := hGloc (s m) hK
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (Real.continuous_exp.comp hf.neg).continuousOn
      have hbound_exp : ∀ x ∈ s m, Real.exp (-(f x)) ≤ max C 0 := fun x hx =>
        le_trans (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hx))
          (le_max_left _ _)
      refine Integrable.mono' (hGi.const_mul (max C 0)) ?_ ?_
      · refine ((hGmeas.norm.pow 2).mul
          (Real.continuous_exp.comp hf.neg).aestronglyMeasurable).mono_measure Measure.restrict_le_self
      · rw [ae_restrict_iff' (hsm m)]
        refine Eventually.of_forall fun x hx => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
          abs_of_nonneg (Real.exp_pos _).le]
        have h1 := hbound_exp x hx
        have h2 : 0 ≤ ‖G x‖ ^ 2 := sq_nonneg _
        calc ‖G x‖ ^ 2 * Real.exp (-(f x)) ≤ ‖G x‖ ^ 2 * max C 0 :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = max C 0 * ‖G x‖ ^ 2 := mul_comm _ _
    · filter_upwards with x
      positivity
  have hfun : (fun x : E => ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(f x))))
      = fun x => ⨆ m, (s m).indicator (fun y : E =>
          ENNReal.ofReal (‖G y‖ ^ 2 * Real.exp (-(f y)))) x := (funext hpoint).symm
  rw [hfun, hMCT]
  simp only [hterm, ciSup_const]


/-- If the weak-gradient identity `∫ ψ ⟪v, G⟫ = -∫ (Dψ)v · g` holds for all smooth compactly
supported `ψ` and all `v`, and one of the integrals on the right is nonzero, and `g` is
locally integrable (so that the relevant functionals are honest and additive), then `G` is
a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_exists_fderiv_integral_ne_zero
    (g : E → ℝ) (G : E → E)
    (hgmeas : AEStronglyMeasurable g volume)
    (hgl : LocallyIntegrable g volume)
    (hG3 : ∀ (ψ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G x) = -∫ x, (fderiv ℝ ψ x) v * g x)
    (hne : ∃ (ψ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      ∫ x, (fderiv ℝ ψ x) v * g x ≠ 0) :
    AEStronglyMeasurable G volume := by
  classical
  -- integrability of the pairing `(Dψ x) v * g x`
  have hInt : ∀ (ψ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Integrable (fun x => (fderiv ℝ ψ x) v * g x) volume := by
    intro ψ v hψ hψc
    have hcont : Continuous (fun x : E => (fderiv ℝ ψ x) v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x : E => (fderiv ℝ ψ x) v) := hψc.fderiv_apply (𝕜 := ℝ) v
    have h := hgl.integrable_smul_left_of_hasCompactSupport hcont hcs
    simpa using h
  -- additivity in the test function
  have hadd : ∀ (ψ χ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∫ x, (fderiv ℝ (fun y => ψ y + χ y) x) v * g x)
        = (∫ x, (fderiv ℝ ψ x) v * g x) + (∫ x, (fderiv ℝ χ x) v * g x) := by
    intro ψ χ v hψ hψc hχ hχc
    have hpoint : ∀ x : E, (fderiv ℝ (fun y => ψ y + χ y) x) v * g x
        = (fderiv ℝ ψ x) v * g x + (fderiv ℝ χ x) v * g x := by
      intro x
      have hd : fderiv ℝ (fun y : E => ψ y + χ y) x = fderiv ℝ ψ x + fderiv ℝ χ x :=
        fderiv_add ((hψ.contDiffAt (x := x)).differentiableAt (by simp))
          ((hχ.contDiffAt (x := x)).differentiableAt (by simp))
      rw [hd]
      simp only [ContinuousLinearMap.add_apply]
      ring
    rw [show (fun x : E => (fderiv ℝ (fun y => ψ y + χ y) x) v * g x)
        = (fun x : E => (fderiv ℝ ψ x) v * g x + (fderiv ℝ χ x) v * g x) from funext hpoint]
    exact integral_add (hInt ψ v hψ hψc) (hInt χ v hχ hχc)
  -- additivity in the direction
  have hlin : ∀ (ψ : E → ℝ) (v w : E), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, (fderiv ℝ ψ x) (v + w) * g x)
        = (∫ x, (fderiv ℝ ψ x) v * g x) + (∫ x, (fderiv ℝ ψ x) w * g x) := by
    intro ψ v w hψ hψc
    have hpoint : ∀ x : E, (fderiv ℝ ψ x) (v + w) * g x
        = (fderiv ℝ ψ x) v * g x + (fderiv ℝ ψ x) w * g x := by
      intro x
      rw [map_add]
      ring
    rw [show (fun x : E => (fderiv ℝ ψ x) (v + w) * g x)
        = (fun x : E => (fderiv ℝ ψ x) v * g x + (fderiv ℝ ψ x) w * g x) from funext hpoint]
    exact integral_add (hInt ψ v hψ hψc) (hInt ψ w hψ hψc)
  -- a nonzero pairing forces measurability of the corresponding product
  have haesm_of_ne : ∀ (w : E) (ψ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, (fderiv ℝ ψ x) w * g x) ≠ 0 →
      AEStronglyMeasurable (fun x => ψ x * inner ℝ w (G x)) volume := by
    intro w ψ hψ hψc hne0
    by_contra h
    have hzero : (∫ x, ψ x * inner ℝ w (G x)) = 0 := integral_non_aestronglyMeasurable h
    have hg := hG3 ψ w hψ hψc
    rw [hzero] at hg
    exact hne0 (by linarith)
  -- main step: if some direction has a nonzero pairing, then every test function works
  have step1 : ∀ (w : E),
      (∃ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
        (∫ x, (fderiv ℝ ψ x) w * g x) ≠ 0) →
      ∀ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        AEStronglyMeasurable (fun x => χ x * inner ℝ w (G x)) volume := by
    intro w ⟨φ, hφcd, hφc, hφne⟩ χ hχcd hχc
    by_cases hχne : (∫ x, (fderiv ℝ χ x) w * g x) = 0
    · have hsum : (∫ x, (fderiv ℝ (fun y => χ y + φ y) x) w * g x) ≠ 0 := by
        rw [hadd χ φ w hχcd hχc hφcd hφc, hχne, zero_add]
        exact hφne
      have h1 := haesm_of_ne w (fun y => χ y + φ y) (hχcd.add hφcd) (hχc.add hφc) hsum
      have h2 := haesm_of_ne w φ hφcd hφc hφne
      have heq : (fun x : E => χ x * inner ℝ w (G x))
          = fun x => (χ x + φ x) * inner ℝ w (G x) - φ x * inner ℝ w (G x) := by
        funext x; ring
      rw [heq]
      exact h1.sub h2
    · exact haesm_of_ne w χ hχcd hχc hχne
  obtain ⟨ψ₀, v₀, hψ₀cd, hψ₀c, hψ₀ne⟩ := hne
  -- for every direction, `χ * ⟪v, G⟫` is a.e. strongly measurable
  have hkey : ∀ (v : E), ∀ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      AEStronglyMeasurable (fun x => χ x * inner ℝ v (G x)) volume := by
    intro v χ hχcd hχc
    by_cases hv : ∃ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
        (∫ x, (fderiv ℝ ψ x) v * g x) ≠ 0
    · exact step1 v hv χ hχcd hχc
    · push_neg at hv
      -- `v` lies in the kernel subspace; add `v₀` (which is outside it) to leave it
      have hvw : ∃ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
          (∫ x, (fderiv ℝ ψ x) (v + v₀) * g x) ≠ 0 := by
        refine ⟨ψ₀, hψ₀cd, hψ₀c, ?_⟩
        rw [hlin ψ₀ v v₀ hψ₀cd hψ₀c, hv ψ₀ hψ₀cd hψ₀c, zero_add]
        exact hψ₀ne
      have h1 := step1 (v + v₀) hvw χ hχcd hχc
      have h2 := step1 v₀ ⟨ψ₀, hψ₀cd, hψ₀c, hψ₀ne⟩ χ hχcd hχc
      have heq : (fun x : E => χ x * inner ℝ v (G x))
          = fun x => χ x * inner ℝ (v + v₀) (G x) - χ x * inner ℝ v₀ (G x) := by
        funext x
        rw [inner_add_left]
        ring
      rw [heq]
      exact h1.sub h2
  -- a bump function equal to one on a ball
  have hbump : ∀ j : ℕ, ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ Metric.closedBall (0 : E) j, χ x = 1 := by
    intro j
    refine ⟨(⟨(j : ℝ) + 1, (j : ℝ) + 2, by positivity, by linarith⟩ : ContDiffBump (0 : E)),
      ContDiffBump.contDiff _, ContDiffBump.hasCompactSupport _, ?_⟩
    intro x hx
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    push_cast
    linarith
  have hcover : (⋃ j : ℕ, Metric.closedBall (0 : E) j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_iUnion.mpr ⟨⌈‖x‖⌉₊, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Nat.le_ceil _
  -- each coordinate is a.e. strongly measurable
  have hlocAE : ∀ v : E, AEStronglyMeasurable (fun x => inner ℝ v (G x)) volume := by
    intro v
    rw [← Measure.restrict_univ (μ := (volume : Measure E)), ← hcover]
    refine (aestronglyMeasurable_iUnion_iff).mpr (fun j => ?_)
    obtain ⟨χ, hχcd, hχc, hχ1⟩ := hbump j
    refine ((hkey v χ hχcd hχc).restrict).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' (Metric.isClosed_closedBall.measurableSet)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [hχ1 x hx]
    ring
  -- conclude
  have hsumae : AEStronglyMeasurable
      (fun x : E => ∑ i : Fin n, inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) (G x)
        • ((EuclideanSpace.basisFun (Fin n) ℝ) i)) volume := by
    have hfun : (fun x : E => ∑ i : Fin n,
          inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) (G x)
            • ((EuclideanSpace.basisFun (Fin n) ℝ) i))
        = (∑ i : Fin n, fun x : E => inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) (G x)
            • ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
      funext x
      simp [Finset.sum_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i _ => (hlocAE ((EuclideanSpace.basisFun (Fin n) ℝ) i)).smul_const _)
  refine hsumae.congr (Filter.Eventually.of_forall (fun x => ?_))
  exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' (G x)

/-- On Euclidean space: a locally `L²` weak solution `g` of `∇·(e^{-f}∇g) = 0` (with `f` smooth)
is almost everywhere constant. -/
theorem weak_solution_const_of_weakGradient_euclidean {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ 2 f)
    (hgmeas : AEStronglyMeasurable g volume)
    (hg2 : Integrable (fun x => g x ^ 2 * Real.exp (-(f x))) volume)
    (hG1 : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IntegrableOn (fun x => ‖G x‖ ^ 2) K volume)
    (hG2 : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x)) (G x)
        * Real.exp (-(f x)) = 0)
    (hG3 : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G x) = -∫ x, (fderiv ℝ ψ x) v * g x) :
    ∃ c : ℝ, g =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f x))))] fun _ => c := by
  classical
  have hgloc : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IntegrableOn (fun x => g x ^ 2) K volume :=
    fun K hK => integrableOn_sq_of_integrable_sq_mul_exp_neg f g hf.continuous hg2 K hK
  have hgl : LocallyIntegrable g volume :=
    Commons.Analysis.Measure.locallyIntegrable_of_aestronglyMeasurable_of_integrableOn_sq hgmeas hgloc
  -- Every weak-gradient integral of `g` vanishes.
  have hkey : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, (fderiv ℝ ψ x) v * g x = 0 := by
    intro ψ v hψ hψc
    by_contra hz
    have hGmeas : AEStronglyMeasurable G volume :=
      aestronglyMeasurable_of_exists_fderiv_integral_ne_zero g G hgmeas hgl hG3
        ⟨ψ, v, hψ, hψc, hz⟩
    have henergy : ∀ η : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
        ∫ x, η x ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x))
          = -2 * ∫ x, η x * g x * (fderiv ℝ η x) (G x) * Real.exp (-(f x)) :=
      fun η hη hηc =>
        weighted_energy_identity_moll_measurable f g G hgmeas hGmeas hf hgloc hG1 hG3 hG2 η hη hηc
    have hzero : ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(f x))) = 0 :=
      weighted_energy_cutoff_zero_aux f g G hf.continuous hGmeas hg2 hG1 henergy
    -- hence `‖G‖² e^{-f}` vanishes a.e., and therefore so does `G`
    have hFae : (fun x => ‖G x‖ ^ 2 * Real.exp (-(f x))) =ᵐ[volume] 0 := by
      have hm : AEMeasurable (fun x => ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(f x)))) volume :=
        ENNReal.measurable_ofReal.comp_aemeasurable (aestronglyMeasurable_iff_aemeasurable.mp ?_)
      · have := (lintegral_eq_zero_iff' hm).mp hzero
        filter_upwards [this] with x hx
        have hle : ‖G x‖ ^ 2 * Real.exp (-(f x)) ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
        exact le_antisymm hle (by positivity)
      · exact ((continuous_norm.comp_aestronglyMeasurable hGmeas).pow 2).mul
          (Real.continuous_exp.comp (hf.continuous.neg)).aestronglyMeasurable
    have hGae : G =ᵐ[volume] 0 := by
      filter_upwards [hFae] with x hx
      have h2 : ‖G x‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp hx with h | h
        · exact h
        · exact absurd h (Real.exp_ne_zero _)
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    have h0 : ∫ x, ψ x * inner ℝ v (G x) = 0 := by
      have hae : (fun x => ψ x * inner ℝ v (G x)) =ᵐ[volume] (fun _ => (0 : ℝ)) := by
        filter_upwards [hGae] with x hx
        rw [hx]
        simp
      rw [integral_congr_ae hae]
      simp
    rw [hG3 ψ v hψ hψc] at h0
    exact hz (neg_eq_zero.mp h0)
  obtain ⟨c, hc⟩ := ae_const_of_forall_deriv_integral_zero g hgl hkey
  exact ⟨c, (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-(f x))))).ae_eq hc⟩




end Weyl

open _root_.MeasureTheory Filter Function Metric Finset ENNReal
open scoped SchwartzMap ContDiff Topology ENNReal Laplacian LineDeriv

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Elementary complexification facts -/

private def cplxF (u : E → ℝ) : E → ℂ := fun x => ((u x : ℝ) : ℂ)

private lemma cplxF_apply (u : E → ℝ) (x : E) : cplxF u x = ((u x : ℝ) : ℂ) := rfl

/-- Measurability of `x ↦ ofReal (exp (-(f x)))`. -/
private lemma measurable_ofReal_exp_neg {f : E → ℝ} (hf : Measurable f) :
    Measurable (fun x : E => ENNReal.ofReal (Real.exp (-(f x)))) := by
  have h1 : Measurable (fun x : E => -(f x)) := hf.neg
  have h2 : Measurable (fun x : E => Real.exp (-(f x))) := Real.measurable_exp.comp h1
  exact ENNReal.measurable_ofReal.comp h2

private lemma fderiv_cplxF (u : E → ℝ) {x : E} (hd : DifferentiableAt ℝ u x) (v : E) :
    fderiv ℝ (cplxF u) x v = ((fderiv ℝ u x v : ℝ) : ℂ) := by
  have h : HasFDerivAt (cplxF u)
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ u x)) x :=
    (Complex.ofRealCLM.hasFDerivAt (x := u x)).comp x (hd.hasFDerivAt)
  rw [h.fderiv]
  rfl

private lemma laplacian_cplxF (u : E → ℝ) {x : E} (hd : ContDiffAt ℝ 2 u x) :
    Laplacian.laplacian (cplxF u) x = ((Laplacian.laplacian u x : ℝ) : ℂ) := by
  have h := hd.laplacian_CLM_comp_left (l := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ))
  have h' : Laplacian.laplacian (fun x : E => ((u x : ℝ) : ℂ)) x = ((Laplacian.laplacian u x : ℝ) : ℂ) := h
  exact h'

/-- The expansion of a scalar product along an orthonormal basis. -/
private lemma sum_fderiv_mul_eq_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f u : E → ℝ) (x : E) :
    (∑ i, fderiv ℝ f x (b i) * fderiv ℝ u x (b i))
      = inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) := by
  have h1 : ∀ i, fderiv ℝ f x (b i)
      = inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) (b i) :=
    fun i => (InnerProductSpace.toDual_symm_apply (x := b i)).symm
  have h2 : ∀ i, fderiv ℝ u x (b i)
      = inner ℝ (b i) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) := by
    intro i
    rw [real_inner_comm]
    exact (InnerProductSpace.toDual_symm_apply (x := b i)).symm
  calc (∑ i, fderiv ℝ f x (b i) * fderiv ℝ u x (b i))
      = ∑ i, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) (b i)
          * inner ℝ (b i) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) :=
        Finset.sum_congr rfl fun i _ => by rw [h1 i, h2 i]
    _ = inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) :=
        b.sum_inner_mul_inner _ _

/-! ## Absolute continuity of Lebesgue measure with respect to `e^{-f} dx` -/

private lemma volume_absolutelyContinuous_gmu (f : E → ℝ) (hf : ContDiff ℝ 2 f) :
    (volume : Measure E) ≪ volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x)))) := by
  intro S hS
  rw [withDensity_apply' _ S] at hS
  have hmeas : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-(f x)))) :=
    measurable_ofReal_exp_neg hf.continuous.measurable
  have h2 : ∀ᵐ x ∂((volume : Measure E).restrict S),
      ENNReal.ofReal (Real.exp (-(f x))) = 0 :=
    (lintegral_eq_zero_iff hmeas).mp hS
  have h3 := ae_iff.mp h2
  have h4 : {x : E | ¬(ENNReal.ofReal (Real.exp (-(f x))) = 0)} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro h
    have hle : Real.exp (-(f x)) ≤ 0 := ENNReal.ofReal_eq_zero.mp h
    exact absurd (Real.exp_pos (-(f x))) (not_lt.mpr hle)
  rw [h4] at h3
  simpa using h3

/-! ## Weyl's lemma : `psi` lies in `H^1` -/

set_option maxHeartbeats 1000000 in
theorem memSobolev_one_of_weak_solution
    (f ψ : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hψ : MemLp (fun x : E => ((ψ x : ℝ) : ℂ)) 2 (volume : Measure E))
    (hψf : MemLp (fun x : E => ((ψ x * ‖fderiv ℝ f x‖ : ℝ) : ℂ)) 2 (volume : Measure E))
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x : E, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
        - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ))) = 0) :
    TemperedDistribution.MemSobolev 1 2
      (↑(hψ.toLp (fun x : E => ((ψ x : ℝ) : ℂ))) : TemperedDistribution E ℂ) :=
  Commons.Analysis.Sobolev.memSobolev_one_of_weak_solutionH1
    (fun T hT => Commons.Analysis.Schwartz.eq_zero_of_forall_hasCompactSupport T hT)
    f ψ hf hψ hψf hw

/-- **Extraction of the weak gradient.** -/
theorem exists_weakGradient_of_memSobolev_one
    (f g ψ : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : MemLp g 2 (volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x))))))
    (hψeq : ψ =ᵐ[(volume : Measure E)] fun x => g x * Real.exp (-(f x)))
    (hψ : MemLp (fun x : E => ((ψ x : ℝ) : ℂ)) 2 (volume : Measure E))
    (hspec : TemperedDistribution.MemSobolev 1 2
      (↑(hψ.toLp (fun x : E => ((ψ x : ℝ) : ℂ))) : TemperedDistribution E ℂ))
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x : E, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
        - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ))) = 0) :
    ∃ G : E → E,
      (∀ K : Set E, IsCompact K → IntegrableOn (fun x => ‖G x‖ ^ 2) K volume) ∧
      (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) (G x)
          * Real.exp (-(f x)) = 0) ∧
      (∀ (φ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, φ x * inner ℝ v (G x) = -∫ x, (fderiv ℝ φ x) v * g x) :=
  Commons.Analysis.Sobolev.weakGradient_of_memSobolev_one
    f g ψ hf hg hψeq hψ hspec hw

/-! ## The closing argument -/

/-- **Closing argument (general form).**  A locally `L^2` weak solution `g` of the weighted
Laplacian equation with weak gradient `G` is almost everywhere constant. -/
theorem weak_solution_const_of_weakGradient
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hgmeas : AEStronglyMeasurable g volume)
    (hg2 : Integrable (fun x => g x ^ 2 * Real.exp (-(f x))) volume)
    (G : E → E)
    (hG1 : ∀ K : Set E, IsCompact K → IntegrableOn (fun x => ‖G x‖ ^ 2) K volume)
    (hG2 : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ x)) (G x)
        * Real.exp (-(f x)) = 0)
    (hG3 : ∀ (ψ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G x) = -∫ x, (fderiv ℝ ψ x) v * g x) :
    ∃ c : ℝ, g =ᵐ[volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x))))]
      fun _ => c :=
  Commons.Analysis.GaussianMeasure.weak_solution_const_of_weakGradient_transfer
    (fun {n : ℕ} f' g' G' hf' hgm' hg2' hG1' hG2' hG3' =>
      weak_solution_const_of_weakGradient_euclidean
        f' g' G' hf' hgm' hg2' hG1' hG2' hG3')
    f g hf hgmeas hg2 G hG1 hG2 hG3

/-! ## The target theorem -/

/-- **Weak solutions of the weighted Laplacian are constant.** -/
theorem weighted_laplacian_weak_solution_const_cinfty {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E]
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2)
    (hg : MemLp g 2 (volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x))))))
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x : E, ((- Laplacian.laplacian φ x
            + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x))) * g x)
          * Real.exp (-(f x))) = 0) :
    ∃ c : ℝ, g =ᵐ[volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x))))]
      fun _ => c := by
  classical
  -- the density of the weighted measure
  set ν : Measure E := volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x)))) with hν
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_withDensity_exp_neg f hf hconv
  -- growth bound on the gradient of `f`
  have hgf' : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ := by
    obtain ⟨C, hC, N, hN⟩ := hgf
    exact ⟨C, hC, N, fun x v => (hN x v).1⟩
  set ψ : E → ℝ := fun x => g x * Real.exp (-(f x)) with hψdef
  obtain ⟨hψ, hψf₀⟩ := Commons.Analysis.Elliptic.memLp_psi_and_grad hf hconv hgf' hg
  have hψf : MemLp (fun x : E => ((ψ x * ‖fderiv ℝ f x‖ : ℝ) : ℂ)) 2 (volume : Measure E) := by
    convert hψf₀ using 1
    ext x
    simp only [hψdef]
    push_cast
    ring
  -- the very weak equation transported to `psi`
  have hwψ : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x : E, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
        - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ))) = 0 := by
    intro φ hd hc
    set hφ : E → ℝ := fun x => ((- Laplacian.laplacian φ x
        + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x))) * g x)
        * Real.exp (-(f x)) with hφdef
    have h : (∫ x : E, hφ x : ℝ) = 0 := by
      rw [hφdef]
      exact hw φ hd hc
    have key : ∀ x : E,
        ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
          - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ))
        = - ((hφ x : ℝ) : ℂ) := by
      intro x
      simp only [hψdef, hφdef]
      push_cast
      ring
    have hInt : (∫ x : E, ((hφ x : ℝ) : ℂ)) = (((∫ x : E, hφ x : ℝ)) : ℂ) :=
      integral_ofReal
    calc (∫ x : E, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
          - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ)))
        = ∫ x : E, - ((hφ x : ℝ) : ℂ) :=
          integral_congr_ae (Filter.Eventually.of_forall key)
      _ = -(∫ x : E, ((hφ x : ℝ) : ℂ)) := integral_neg _
      _ = -(((∫ x : E, hφ x : ℝ)) : ℂ) := by rw [hInt]
      _ = 0 := by rw [h]; simp
  have hspec := memSobolev_one_of_weak_solution f ψ hf hψ hψf hwψ
  have hψeq : ψ =ᵐ[(volume : Measure E)] fun x => g x * Real.exp (-(f x)) :=
    Filter.EventuallyEq.of_eq rfl
  obtain ⟨G, hG1, hG2, hG3⟩ :=
    exists_weakGradient_of_memSobolev_one f g ψ hf hg hψeq hψ hspec hwψ
  -- measurability and square-integrability of `g`
  have hgmeas : AEStronglyMeasurable g volume :=
    (hg.aestronglyMeasurable.mono_ac (volume_absolutelyContinuous_gmu f hf))
  have hg2 : Integrable (fun x => g x ^ 2 * Real.exp (-(f x))) volume := by
    have h2 : Integrable (fun x => ‖g x‖ ^ 2) ν :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    have hmeas : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-(f x)))) :=
      measurable_ofReal_exp_neg hf.continuous.measurable
    have h3 := (integrable_withDensity_iff (μ := (volume : Measure E)) hmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp h2
    simpa only [Function.comp_apply, Pi.neg_apply, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      Real.norm_eq_abs, sq_abs] using h3
  exact weak_solution_const_of_weakGradient f g hf hgmeas hg2 G hG1 hG2 hG3

end

open MeasureTheory Real
open scoped Real ENNReal
noncomputable section

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The measure `e^{-f} dx` is invariant under `x ↦ -x` when `f` is even. -/
private lemma isNegInvariant_withDensity_of_even (f : E → ℝ) (hf : Measurable f)
    (heven : ∀ x : E, f (-x) = f x) :
    (volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x))))).IsNegInvariant := by
  set w : E → ENNReal := fun x => ENNReal.ofReal (Real.exp (-(f x))) with hwdef
  have hwmeas : Measurable w :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf.neg)
  have hweven : ∀ x : E, w (-x) = w x := by
    intro x; simp only [hwdef, heven x]
  have hneg : Measurable (fun x : E => -x) := measurable_neg
  have hmp : MeasurePreserving (fun x : E => -x) (volume : Measure E) volume :=
    Measure.measurePreserving_neg _
  refine ⟨?_⟩
  rw [Measure.neg_def]
  ext s hs
  rw [Measure.map_apply hneg hs, withDensity_apply _ (hneg hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hneg hs) w]
  have hrw : (fun x => ((fun x : E => -x) ⁻¹' s).indicator w x) = fun x => (s.indicator w) (-x) := by
    funext x
    by_cases h : -x ∈ s
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr h), Set.indicator_of_mem h]
      exact (hweven x).symm
    · rw [Set.indicator_of_notMem (by simpa using h), Set.indicator_of_notMem h]
  rw [hrw]
  rw [← lintegral_map (hwmeas.indicator hs) hneg]
  rw [hmp.map_eq]
  rw [lintegral_indicator hs w]

/-! ## Density of the range of the weighted Laplacian

The proof reduces (via a Hilbert-space orthogonal-complement argument) to the statement that every
`L²(e^{-f})` weak solution of `M g = 0` (where `M u = -Δu + ⟪∇f, ∇u⟫`) is a.e. constant; this is the
Weyl-type regularity lemma `weighted_laplacian_weak_solution_const_cinfty` from the commons.
The remaining steps are elementary: one takes a finite linear combination `∑ cᵢ M φᵢ` close to `h`,
symmetrizes it (the even part is an orthogonal projection for the even measure `e^{-f}dx`) and
rewrites it as `M u` for the even, compactly supported smooth `u = ∑ cᵢ (φᵢ + φᵢ∘(-·))/2`.
-/

private abbrev grd (φ : E → ℝ) : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)
private abbrev Mlap (f u : E → ℝ) : E → ℝ :=
  fun x => -Laplacian.laplacian u x + inner ℝ (grd f x) (grd u x)
private abbrev gmu (f : E → ℝ) : Measure E :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (-(f x)))

private lemma integral_gmu (f Φ : E → ℝ) (hf : Measurable f) :
    ∫ x, Φ x ∂(gmu f) = ∫ x, Φ x * Real.exp (-(f x)) := by
  rw [gmu, integral_withDensity_eq_integral_toReal_smul _
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]; ring
  · exact (Real.measurable_exp.comp hf.neg).ennreal_ofReal


private lemma memLp_gmu_integrable (f g : E → ℝ) (hf : Measurable f)
    (hg : MemLp g 2 (gmu f)) :
    Integrable (fun x => g x ^ 2 * Real.exp (-(f x))) := by
  have h2 : Integrable (fun x => ‖g x‖ ^ 2) (gmu f) :=
    (memLp_two_iff_integrable_sq_norm (μ := gmu f) hg.aestronglyMeasurable).mp hg
  have h3 := (integrable_withDensity_iff (μ := (volume : Measure E))
    ((Real.measurable_exp.comp hf.neg).ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp h2
  simpa only [Function.comp_apply, Pi.neg_apply, ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.norm_eq_abs, sq_abs] using h3

private lemma mlap_finset_sum (f : E → ℝ) {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (u : ι → E → ℝ) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hlin : ∀ (a b : ℝ) (p q : E → ℝ), ContDiff ℝ 2 p → ContDiff ℝ 2 q →
      Mlap f (fun y => a * p y + b * q y) = fun x => a * Mlap f p x + b * Mlap f q x) :
    Mlap f (fun x => ∑ i ∈ t, c i * u i x) = fun x => ∑ i ∈ t, c i * Mlap f (u i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      funext x; simp only [Finset.sum_empty]
      have h1 : grd (fun _ : E => (0:ℝ)) x = 0 := by simp [grd]
      simp [Mlap, h1]
  | insert a t ha ih =>
      have hc : ContDiff ℝ 2 (fun x => ∑ i ∈ t, c i * u i x) :=
        ContDiff.sum fun i _ => (hu i).const_smul (c i)
      have hgoal : (fun x => ∑ i ∈ insert a t, c i * u i x)
          = (fun y => c a * u a y + 1 * (∑ i ∈ t, c i * u i y)) := by
        funext x; rw [Finset.sum_insert ha]; ring
      rw [hgoal, hlin (c a) 1 (u a) (fun y => ∑ i ∈ t, c i * u i y) (hu a) hc]
      funext x; rw [Finset.sum_insert ha]; simp only [one_mul]; congr 1; exact congrFun ih x

private lemma mlap_symm (f u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (hlin : ∀ (a b : ℝ) (p q : E → ℝ), ContDiff ℝ 2 p → ContDiff ℝ 2 q →
      Mlap f (fun y => a * p y + b * q y) = fun x => a * Mlap f p x + b * Mlap f q x)
    (hreflect : ∀ v : E → ℝ, ContDiff ℝ 2 v → ∀ x : E,
      Mlap f (fun y => v (-y)) x = Mlap f v (-x)) :
    Mlap f (fun x => (u x + u (-x)) / 2) = fun x => (Mlap f u x + Mlap f u (-x)) / 2 := by
  have hcomp : ContDiff ℝ 2 (fun y : E => u (-y)) := hu.comp contDiff_neg
  have hkey : (fun x => (u x + u (-x)) / 2)
      = (fun y => (1/2) * u y + (1/2) * (fun z => u (-z)) y) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hkey, hlin (1/2) (1/2) u (fun y => u (-y)) hu hcomp]
  funext x; rw [hreflect u hu x]; ring

private theorem aux (f h : E → ℝ)
    (hfm : Measurable f)
    (hμ : IsFiniteMeasure (gmu f))
    (hh_memLp : MemLp h 2 (gmu f))
    (hmean_mu : ∫ x, h x ∂(gmu f) = 0)
    (hheven : ∀ x, h (-x) = h x)
    (hMlap_memLp : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      MemLp (Mlap f φ) 2 (gmu f))
    (hcss : ∀ (n : ℕ) (c : Fin n → ℝ) (u : Fin n → E → ℝ),
      (∀ i, HasCompactSupport (u i)) →
      HasCompactSupport (fun x => ∑ i, c i * u i x))
    (crux : ∀ g : E → ℝ, MemLp g 2 (gmu f) →
      (∀ φ : E → ℝ, ContDiff ℝ (⊤:ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (Mlap f φ x * g x) * Real.exp (-(f x))) = 0) →
      ∃ c : ℝ, g =ᵐ[gmu f] fun _ => c)
    (hlin : ∀ (a b : ℝ) (p q : E → ℝ), ContDiff ℝ 2 p → ContDiff ℝ 2 q →
      Mlap f (fun y => a * p y + b * q y) = fun x => a * Mlap f p x + b * Mlap f q x)
    (hreflect : ∀ v : E → ℝ, ContDiff ℝ 2 v → ∀ x : E, Mlap f (fun y => v (-y)) x = Mlap f v (-x))
    (hsymm : ∀ {h₁ w : E → ℝ}, (∀ x, h₁ (-x) = h₁ x) → MemLp w 2 (gmu f) → MemLp h₁ 2 (gmu f) →
      ∫ x, (h₁ x - (w x + w (-x)) / 2) ^ 2 ∂(gmu f) ≤ ∫ x, (h₁ x - w x) ^ 2 ∂(gmu f))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∫ x, (Mlap f u x - h x) ^ 2 * Real.exp (-(f x))) ≤ ε := by
  classical
  set S : Set (E → ℝ) := {s | ∃ φ : E → ℝ, ContDiff ℝ (⊤:ℕ∞) φ ∧ HasCompactSupport φ ∧ s = Mlap f φ} with hSdef
  have hS : ∀ s ∈ S, MemLp s 2 (gmu f) := by
    rintro s ⟨φ, hφ, hcφ, rfl⟩; exact hMlap_memLp φ hφ hcφ
  have horth : ∀ g : E → ℝ, MemLp g 2 (gmu f) →
      (∀ s ∈ S, ∫ x, g x * s x ∂(gmu f) = 0) → ∃ c : ℝ, g =ᵐ[gmu f] fun _ => c := by
    intro g hg hgs
    refine crux g hg ?_
    intro φ hφ hcφ
    have hs : Mlap f φ ∈ S := ⟨φ, hφ, hcφ, rfl⟩
    have h0 := hgs (Mlap f φ) hs
    rw [integral_gmu f (fun x => g x * Mlap f φ x) hfm] at h0
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h0
  obtain ⟨n, c, s, hsS, hsmem, hbound⟩ :=
    Commons.Analysis.InnerProductSpace.combination_close_of_orthogonal_const (gmu f) S hS horth h hh_memLp hmean_mu ε hε
  choose φ hφc hcφc hs_eq using hsS
  set ψ : Fin n → E → ℝ := fun i x => (φ i x + φ i (-x)) / 2 with hψdef
  have hφ2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => (hφc i).of_le (WithTop.coe_le_coe.mpr le_top)
  have hψc : ∀ i, ContDiff ℝ (⊤:ℕ∞) (ψ i) := fun i => by
    have hcomp : ContDiff ℝ (⊤:ℕ∞) (fun y : E => φ i (-y)) := (hφc i).comp contDiff_neg
    have hsum : ContDiff ℝ (⊤:ℕ∞) (fun x : E => φ i x + φ i (-x)) := (hφc i).add hcomp
    have : (ψ i) = fun x : E => (φ i x + φ i (-x)) / 2 := rfl
    rw [this]; exact hsum.div_const 2
  have hψ2 : ∀ i, ContDiff ℝ 2 (ψ i) := fun i => (hψc i).of_le (WithTop.coe_le_coe.mpr le_top)
  have hψcs : ∀ i, HasCompactSupport (ψ i) := fun i => by
    have hcomp : HasCompactSupport (fun y : E => φ i (-y)) :=
      (hcφc i).comp_homeomorph (Homeomorph.neg E)
    have hsum : HasCompactSupport (fun x : E => φ i x + φ i (-x)) := (hcφc i).add hcomp
    have hsm : HasCompactSupport (fun x : E => (1/2:ℝ) • (φ i x + φ i (-x))) :=
      hsum.smul_left (f := fun _ : E => (1/2:ℝ))
    have heq : (fun x : E => (1/2:ℝ) • (φ i x + φ i (-x)))
        = fun x : E => (1/2:ℝ) * (φ i x + φ i (-x)) := by funext x; rw [smul_eq_mul]
    rw [heq] at hsm
    have : (ψ i) = fun x : E => (1/2:ℝ) * (φ i x + φ i (-x)) := by
      funext x; simp only [hψdef]; ring
    rw [this]; exact hsm
  refine ⟨fun x => ∑ i, c i * ψ i x, ?_, ?_, ?_, ?_⟩
  · exact ContDiff.sum fun i _ => (hψc i).const_smul (c i)
  · exact hcss n c ψ hψcs
  · intro x
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hψdef, neg_neg]
    ring
  · set w : E → ℝ := fun x => ∑ i, c i * s i x with hwdef
    have hw_memLp : MemLp w 2 (gmu f) := by
      have hh := hh_memLp.sub hsmem
      have heq : (h - fun x => h x - ∑ i, c i * s i x) = w := by
        funext x; simp only [Pi.sub_apply, hwdef]; ring
      rwa [heq] at hh
    have hMlap_u : Mlap f (fun x => ∑ i, c i * ψ i x) = fun x => (w x + w (-x)) / 2 := by
      rw [mlap_finset_sum f Finset.univ c ψ hψ2 hlin]
      have h1 : (fun x => ∑ i : Fin n, c i * Mlap f (ψ i) x)
          = fun x => ∑ i, c i * ((s i x + s i (-x)) / 2) := by
        funext x
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        rw [hs_eq i, mlap_symm f (φ i) (hφ2 i) hlin hreflect]
      rw [h1]
      funext x
      simp only [hwdef, Finset.sum_apply]
      rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hmain := hsymm (h₁ := h) (w := w) hheven hw_memLp hh_memLp
    calc ∫ x, (Mlap f (fun x => ∑ i, c i * ψ i x) x - h x) ^ 2 * Real.exp (-(f x))
        = ∫ x, (Mlap f (fun x => ∑ i, c i * ψ i x) x - h x) ^ 2 ∂(gmu f) :=
          (integral_gmu f _ hfm).symm
      _ = ∫ x, (h x - (w x + w (-x)) / 2) ^ 2 ∂(gmu f) := by
          rw [hMlap_u]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [Pi.sub_apply]; ring
      _ ≤ ∫ x, (h x - w x) ^ 2 ∂(gmu f) := hmain
      _ ≤ ε := hbound


/-- **Density of the range of the weighted Laplacian.**  For an even `C²` potential `f` which is
`2π`-strongly convex and convex after subtracting `π‖x‖²`, and an even `C¹` mean-zero function `h`
with polynomial growth, every `ε > 0` admits an even compactly supported `C^∞` function `u` with
`∫ (M u - h)² e^{-f} ≤ ε`, where `M u = -Δu + ⟪∇f, ∇u⟫`.

(This is the "approximation by `L u`" statement of Cordero-Erausquin–Fradelizi–Maurey; it is
equivalent to `C_c^∞` being a core for `M = ∇^*∇` on `L²(e^{-f})`.) -/
theorem weighted_laplacian_range_dense {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (f h : E → ℝ)
    (hf : ContDiff ℝ 2 f)
    (heven : ∀ x : E, f (-x) = f x)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2)
    (hh : ContDiff ℝ 1 h) (hheven : ∀ x : E, h (-x) = h x)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖)
    (hmean : (∫ x, h x * Real.exp (-(f x))) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∫ x, ((- Laplacian.laplacian u x
            + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) - h x) ^ 2
          * Real.exp (-(f x))) ≤ ε := by
  have hfm : Measurable f := hf.continuous.measurable
  have hμ : IsFiniteMeasure (gmu f) := isFiniteMeasure_withDensity_exp_neg f hf hconv
  haveI hnegi : (gmu f).IsNegInvariant := isNegInvariant_withDensity_of_even f hfm heven
  obtain ⟨Ch, hCh, Nh, hghN⟩ := hgh
  have hh_memLp : MemLp h 2 (gmu f) :=
    memLp_withDensity_exp_neg f h hf hconv hh.continuous
      ⟨Ch, hCh, Nh, fun x => (hghN x 0).1⟩
  have hmean_mu : ∫ x, h x ∂(gmu f) = 0 := by
    rw [integral_gmu f h hfm]; exact hmean
  have hgf_copy := hgf
  obtain ⟨Cf, hCf, Nf, hgfN⟩ := hgf_copy
  have hgf' : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ :=
    ⟨Cf, hCf, Nf, fun x v => (hgfN x v).1⟩
  have hMlap_memLp : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      MemLp (Mlap f φ) 2 (gmu f) :=
    fun φ hφ hcφ => memLp_weightedLaplacian_c2 f φ hf
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hcφ hgf' hμ
  have hcss : ∀ (n : ℕ) (c : Fin n → ℝ) (u : Fin n → E → ℝ),
      (∀ i, HasCompactSupport (u i)) → HasCompactSupport (fun x => ∑ i, c i * u i x) :=
    fun n c u hu => Commons.Topology.Support.hasCompactSupport_finset_sum Finset.univ c u (fun i _ => hu i)
  have hcrux : ∀ g : E → ℝ, MemLp g 2 (gmu f) →
      (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, (Mlap f φ x * g x) * Real.exp (-(f x))) = 0) →
      ∃ c : ℝ, g =ᵐ[gmu f] fun _ => c := by
    intro g hg hw
    exact weighted_laplacian_weak_solution_const_cinfty f g hf hH hconv hgf hg hw
  have hlin : ∀ (a b : ℝ) (p q : E → ℝ), ContDiff ℝ 2 p → ContDiff ℝ 2 q →
      Mlap f (fun y => a * p y + b * q y) = fun x => a * Mlap f p x + b * Mlap f q x :=
    fun a b p q hp hq => laplacian_weighted_linear f a b p q hp hq
  have hreflect : ∀ v : E → ℝ, ContDiff ℝ 2 v → ∀ x : E,
      Mlap f (fun y => v (-y)) x = Mlap f v (-x) :=
    fun v hv => laplacian_weighted_comp_neg hf heven hv
  have hsymm : ∀ {h₁ w : E → ℝ}, (∀ x, h₁ (-x) = h₁ x) → MemLp w 2 (gmu f) →
      MemLp h₁ 2 (gmu f) →
      ∫ x, (h₁ x - (w x + w (-x)) / 2) ^ 2 ∂(gmu f) ≤ ∫ x, (h₁ x - w x) ^ 2 ∂(gmu f) :=
    fun {h₁ w} hh1 hwm hhm => Commons.Analysis.InnerProductSpace.integral_symmPart_sq_le (gmu f) hh1 hwm hhm
  exact aux f h hfm hμ hh_memLp hmean_mu hheven hMlap_memLp hcss hcrux hlin hreflect hsymm ε hε

/-- The whole-space even Poincaré inequality for smooth even strongly-log-concave potentials,
assembled from the range density of the weighted Laplacian and the creation energy bound. -/
private theorem even_poincare_smooth_of_range_density_all : EvenPoincareSmooth := by
  intro m g h hg2 hH hconv hgeven hgg hh hheven hgh
  exact even_poincare_smooth_of_density_mean g h hg2 hH hconv hgeven hgg hh hheven hgh
    (fun k hk hkeven hkg hkmean ε hε =>
      weighted_laplacian_range_dense g k hg2 hgeven hH hconv hgg hk hkeven hkg hkmean ε hε)
    (fun u hu hue hgu => creation_energy_bound_even g u hg2 hgeven hH hconv hgg hu hue hgu)

/-- **The (B)-conjecture input: the even Poincaré inequality for a truncated symmetric Gaussian.**
(Cordero-Erausquin-Fradelizi-Maurey.)  This is the exact statement needed downstream. -/
theorem truncated_symmetric_gaussian_even_poincare {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : Convex ℝ A) (hsym : ∀ x, x ∈ A ↔ -x ∈ A) (hAm : MeasurableSet A)
    (hApos : 0 < ∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (heven : ∀ x, f (-x) = f x)
    (h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A)
    (hg : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A) :
    (∫ x : EuclideanSpace ℝ (Fin n) in A, f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
        / (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
      - ((∫ x : EuclideanSpace ℝ (Fin n) in A, f x * Real.exp (-Real.pi * ‖x‖ ^ 2))
          / (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))) ^ 2
    ≤ (1 / (4 * Real.pi)) *
        ((∫ x : EuclideanSpace ℝ (Fin n) in A, ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
          / (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))) := by
  exact even_poincare_truncated_of_smooth even_poincare_smooth_of_range_density_all
    A hA hsym hAm hApos f hf heven h2 hg

end

end BCD

theorem B_conjecture_diagonal {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    (a b : Fin n → ℝ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (∫ x in (fun x => WithLp.toLp 2 (fun i => Real.exp (a i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ lam
      * (∫ x in (fun x => WithLp.toLp 2 (fun i => Real.exp (b i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ (1 - lam)
      ≤ ∫ x in (fun x => WithLp.toLp 2 (fun i => Real.exp (lam * a i + (1 - lam) * b i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  exact B_conj_of_even_poincare
    (fun {m} A hA hsym hAm hApos f hf heven h2 hg =>
      BCD.truncated_symmetric_gaussian_even_poincare A hA hsym hAm hApos f hf heven h2 hg)
    K hKcvx hKsymm a b lam h0 h1

