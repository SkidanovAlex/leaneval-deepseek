import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.testfun_basic
import Submission.Work.LinnikAreas.Density4.testfun_conv
import Submission.Work.LinnikAreas.Density4.testfun_lapl_pos
import Submission.Work.LinnikAreas.Density4.gT_integrable
import Submission.Work.LinnikAreas.Density4.convT_even
import Submission.Work.LinnikAreas.Density4.convT_eq_zero_of_two_gammaT_le_abs
import Submission.Work.LinnikAreas.Density4.fT_eq_convT
import Submission.Work.LinnikAreas.Density4.convT_integrable
import Submission.Work.NumberTheory.Linnik.scratch_convcos
import Submission.Work.NumberTheory.Linnik.scratch_reF

open scoped BigOperators
open MeasureTheory intervalIntegral

noncomputable section

namespace Work.LinnikAreas.Density4

/-- `gT θ lam` is even (used to apply the convolution-square cosine identity). -/
lemma gT_even_aux (θ lam : ℝ) : ∀ t : ℝ, gT θ lam (-t) = gT θ lam t := by
  intro t
  rw [gT, gT, abs_neg]
  by_cases h : |t| ≤ gammaT θ lam
  · rw [if_pos h, if_pos h, show zetaT θ lam * (-t) = -(zetaT θ lam * t) by ring, Real.cos_neg]
  · rw [if_neg h, if_neg h]

theorem fT_laplace_axis_nonneg {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) :
    ∀ t : ℝ, 0 ≤ (∫ u in (0:ℝ)..(2 * gammaT θ lam),
        Complex.exp (-((Complex.I * (t : ℂ)) * (u : ℂ))) * ((fT θ lam u : ℝ) : ℂ)).re := by
  intro t
  have hγ : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  have h2γ : (0:ℝ) ≤ 2 * gammaT θ lam := by linarith
  have hg_int : Integrable (fun s : ℝ => gT θ lam s) := gT_integrable hθ1 hθ2 hlam
  have hg_even : ∀ v : ℝ, gT θ lam (-v) = gT θ lam v := gT_even_aux θ lam
  have hH_int : Integrable (fun v : ℝ => ∫ s : ℝ, gT θ lam s * gT θ lam (v - s)) :=
    convT_integrable hθ1 hθ2 hlam
  have hH_even : ∀ v : ℝ, (∫ s : ℝ, gT θ lam s * gT θ lam (-v - s))
      = ∫ s : ℝ, gT θ lam s * gT θ lam (v - s) := convT_even hθ1 hθ2 hlam
  have hH_supp : ∀ v : ℝ, 2 * gammaT θ lam ≤ |v| →
      (∫ s : ℝ, gT θ lam s * gT θ lam (v - s)) = 0 :=
    convT_eq_zero_of_two_gammaT_le_abs hθ1 hθ2 hlam
  have hH_eq : ∀ v ∈ Set.Icc (0:ℝ) (2 * gammaT θ lam),
      fT θ lam v = ∫ s : ℝ, gT θ lam s * gT θ lam (v - s) := fT_eq_convT hθ1 hθ2 hlam
  -- Step 1: identify the real part of the complex integral with the real integral.
  have hIint : IntervalIntegrable (fun u : ℝ =>
      Complex.exp (-((Complex.I * (t : ℂ)) * (u : ℂ))) * ((fT θ lam u : ℝ) : ℂ)) volume 0
      (2 * gammaT θ lam) := by
    have hcont : Continuous (fun u : ℝ =>
        Complex.exp (-((Complex.I * (t : ℂ)) * (u : ℂ))) * ((fTclosed θ lam u : ℝ) : ℂ)) :=
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).mul
        (Complex.continuous_ofReal.comp (continuous_fTclosed θ lam))
    have h0 : IntervalIntegrable (fun u : ℝ =>
        Complex.exp (-((Complex.I * (t : ℂ)) * (u : ℂ))) * ((fTclosed θ lam u : ℝ) : ℂ)) volume 0
        (2 * gammaT θ lam) := hcont.intervalIntegrable _ _
    refine h0.congr_uIoo ?_
    intro u hu
    rw [Set.uIoo_of_le h2γ] at hu
    simp only
    rw [fT_eq_fTclosed θ lam u ⟨hu.1.le, hu.2.le⟩]
  rw [Commons.NumberTheory.Linnik.re_laplace_eq (z := Complex.I * (t : ℂ)) (f := fT θ lam) hIint]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    neg_zero, Real.exp_zero, one_mul]
  -- Step 2: the real integral is half of the full-line cosine transform of `gT ⊛ gT`.
  set c : ℝ → ℝ := fun v => Real.cos (t * v) * (∫ s : ℝ, gT θ lam s * gT θ lam (v - s)) with hc
  have hc_int : Integrable c := by
    simp only [hc]
    exact hH_int.bdd_mul
      ((by fun_prop : Continuous fun v : ℝ => Real.cos (t * v))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
  have hnonneg : 0 ≤ ∫ v : ℝ, c v := by
    have h := Commons.NumberTheory.Linnik.convolution_cos_nonneg (g := gT θ lam) hg_int hg_even t
    simpa [hc] using h
  have hsupp : ∀ v, v ∉ Set.Ioc (-(2 * gammaT θ lam)) (2 * gammaT θ lam) → c v = 0 := by
    intro v hv
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    simp only [hc]
    rcases hv with hv | hv
    · rw [hH_supp v (by rw [abs_of_nonpos (by linarith)]; linarith), mul_zero]
    · rw [hH_supp v (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have h1 : IntervalIntegrable c volume (-(2 * gammaT θ lam)) 0 := by
    rw [intervalIntegrable_iff]; exact hc_int.integrableOn
  have h2 : IntervalIntegrable c volume 0 (2 * gammaT θ lam) := by
    rw [intervalIntegrable_iff]; exact hc_int.integrableOn
  have hfull : ∫ v : ℝ, c v = 2 * ∫ v in (0:ℝ)..(2 * gammaT θ lam), c v := by
    have e1 : ∫ v : ℝ, c v = ∫ v in Set.Ioc (-(2 * gammaT θ lam)) (2 * gammaT θ lam), c v := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Ioc (-(2 * gammaT θ lam)) (2 * gammaT θ lam)) hsupp]
    have e2 : ∫ v in Set.Ioc (-(2 * gammaT θ lam)) (2 * gammaT θ lam), c v
        = ∫ v in (-(2 * gammaT θ lam))..(2 * gammaT θ lam), c v := by
      rw [intervalIntegral.integral_of_le (by linarith : -(2 * gammaT θ lam) ≤ 2 * gammaT θ lam)]
    have e3 : ∫ v in (-(2 * gammaT θ lam))..(2 * gammaT θ lam), c v
        = (∫ v in (-(2 * gammaT θ lam))..0, c v) + ∫ v in (0:ℝ)..(2 * gammaT θ lam), c v :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    have e4 : ∫ v in (-(2 * gammaT θ lam))..0, c v = ∫ v in (0:ℝ)..(2 * gammaT θ lam), c v := by
      have hcomp : ∫ v in (-(2 * gammaT θ lam))..(0:ℝ), c v
          = ∫ v in (0:ℝ)..(2 * gammaT θ lam), c (-v) := by
        simpa using (intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 2 * gammaT θ lam) c).symm
      rw [hcomp]
      apply intervalIntegral.integral_congr
      intro v hv
      simp only [hc]
      rw [hH_even v, show t * -v = -(t * v) by ring, Real.cos_neg]
    rw [e1, e2, e3, e4]; ring
  have hkey : ∫ u in (0:ℝ)..(2 * gammaT θ lam), Real.cos (t * u) * fT θ lam u
      = (1/2) * ∫ v : ℝ, c v := by
    have hfin : ∫ v in (0:ℝ)..(2 * gammaT θ lam), c v
        = ∫ u in (0:ℝ)..(2 * gammaT θ lam), Real.cos (t * u) * fT θ lam u := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le h2γ] at hv
      simp only [hc]
      rw [hH_eq v ⟨hv.1, hv.2⟩]
    rw [← hfin, hfull]; ring
  rw [hkey]
  exact mul_nonneg (by norm_num) hnonneg

end Work.LinnikAreas.Density4
