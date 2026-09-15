import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Real.integral_conjugate_fubini
import Submission.Commons.Analysis.Real.integral_deriv_arctan_Ioi
import Submission.Commons.Measure.Real.setIntegral_Iio_neg_eq_Ioi

namespace Commons.Analysis.Real

open MeasureTheory Set
open scoped Topology

/-- Splitting the full-line Poisson kernel integral into the half-line integral of the even part. -/
private lemma poisson_split {φ : ℝ → ℝ} (hφc : Continuous φ) (hc : HasCompactSupport φ)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ t : ℝ, φ t * (σ / (σ ^ 2 + t ^ 2))
      = σ * ∫ u in Set.Ioi (0 : ℝ), (φ u + φ (-u)) / (σ ^ 2 + u ^ 2) := by
  set f : ℝ → ℝ := fun t => φ t / (σ ^ 2 + t ^ 2) with hfdef
  have hf_cont : Continuous f := by
    rw [hfdef]; exact hφc.div (by continuity) (fun t => by positivity)
  have hf_supp : HasCompactSupport f := by
    rw [hfdef]; exact hc.mul_right
  have hf_int : Integrable f := hf_cont.integrable_of_hasCompactSupport hf_supp
  have hL : (∫ t : ℝ, φ t * (σ / (σ ^ 2 + t ^ 2))) = σ * ∫ t : ℝ, f t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [hfdef]; ring
  have hcompl : (∫ t : ℝ, f t) = (∫ t in Set.Ioi (0:ℝ), f t) + ∫ t in Set.Iic (0:ℝ), f t := by
    have h := integral_add_compl (s := Set.Ioi (0:ℝ)) measurableSet_Ioi hf_int
    rw [Set.compl_Ioi] at h
    exact h.symm
  have hrefl : (∫ t in Set.Ioi (0:ℝ), f (-t)) = ∫ t in Set.Iic (0:ℝ), f t := by
    have h := integral_comp_neg_Iic (c := (0:ℝ)) (f := fun x : ℝ => f (-x))
    simp only [neg_neg, neg_zero] at h
    exact h.symm
  have hfnegsupp : HasCompactSupport (fun t : ℝ => f (-t)) :=
    hf_supp.comp_homeomorph (Homeomorph.neg ℝ)
  have hfneg_cont : Continuous (fun t : ℝ => f (-t)) := hf_cont.comp continuous_neg
  have hsum : (∫ t in Set.Ioi (0:ℝ), f t) + ∫ t in Set.Ioi (0:ℝ), f (-t)
      = ∫ t in Set.Ioi (0:ℝ), (f t + f (-t)) := by
    rw [integral_add hf_int.integrableOn
      ((hfneg_cont.integrable_of_hasCompactSupport hfnegsupp).integrableOn)]
  have hfin : (∫ t : ℝ, f t) = ∫ u in Set.Ioi (0:ℝ), (f u + f (-u)) := by
    rw [hcompl, ← hrefl, hsum]
  have hpt : ∀ u : ℝ, f u + f (-u) = (φ u + φ (-u)) / (σ ^ 2 + u ^ 2) := by
    intro u
    simp only [hfdef]
    rw [show σ ^ 2 + (-u) ^ 2 = σ ^ 2 + u ^ 2 by ring]
    ring
  have hfin2 : (∫ t : ℝ, f t) = ∫ u in Set.Ioi (0:ℝ), (φ u + φ (-u)) / (σ ^ 2 + u ^ 2) := by
    rw [hfin]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    exact hpt u
  rw [hL, hfin2]

theorem poissonExtension_eq_integral_conjugate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) {σ : ℝ} (hσ : 0 < σ) :
    (1 / Real.pi) * (∫ t : ℝ, φ t * (σ / (σ ^ 2 + t ^ 2))) - φ 0
      = ∫ s in (0 : ℝ)..σ, (1 / Real.pi) * ∫ u in Set.Ioi (0 : ℝ),
          (deriv φ u - deriv φ (-u)) * (u / (u ^ 2 + s ^ 2)) := by
  have hg1 : ContDiff ℝ 1 (fun u : ℝ => φ u + φ (-u)) :=
    (hφ.add (hφ.comp contDiff_neg)).of_le (by norm_num)
  have hgc : HasCompactSupport (fun u : ℝ => φ u + φ (-u)) :=
    hc.add (hc.comp_homeomorph (Homeomorph.neg ℝ))
  have hderiv : ∀ u : ℝ, deriv (fun u : ℝ => φ u + φ (-u)) u = deriv φ u - deriv φ (-u) := by
    intro u
    have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hd2 : Differentiable ℝ (fun u : ℝ => φ (-u)) := hd.comp differentiable_neg
    have h : (fun u : ℝ => φ u + φ (-u)) = φ + (fun u : ℝ => φ (-u)) := by funext x; rfl
    rw [h, deriv_add hd.differentiableAt hd2.differentiableAt, deriv_comp_neg φ u]
    ring
  have hinner : ∀ s : ℝ,
      (∫ u in Set.Ioi (0:ℝ), (deriv φ u - deriv φ (-u)) * (u/(u^2+s^2)))
        = ∫ u in Set.Ioi (0:ℝ), deriv (fun u : ℝ => φ u + φ (-u)) u * (u/(u^2+s^2)) := by
    intro s
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    show (deriv φ u - deriv φ (-u)) * (u / (u^2+s^2))
        = deriv (fun u : ℝ => φ u + φ (-u)) u * (u / (u^2+s^2))
    rw [hderiv u]
  have hRHS : (∫ s in (0:ℝ)..σ, (1/Real.pi) * ∫ u in Set.Ioi (0:ℝ),
        (deriv φ u - deriv φ (-u)) * (u/(u^2+s^2)))
      = (1/Real.pi) * ∫ s in (0:ℝ)..σ, (∫ u in Set.Ioi (0:ℝ),
          deriv (fun u : ℝ => φ u + φ (-u)) u * (u/(u^2+s^2))) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    exact hinner s
  rw [hRHS, integral_conjugate_fubini hg1 hgc hσ, integral_deriv_arctan_Ioi hg1 hgc hσ]
  rw [poisson_split hφ.continuous hc hσ]
  simp only [neg_zero]
  field_simp
  ring

end Commons.Analysis.Real