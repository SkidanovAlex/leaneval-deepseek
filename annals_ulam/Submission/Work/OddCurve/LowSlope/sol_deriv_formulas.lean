import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs

open Filter Topology

namespace Work.OddCurve.LowSlope

theorem sol_deriv_formulas (n : ℕ) {A B R r : ℝ → ℝ} {α : ℝ}
    (hR : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R α)
    (hr : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r α)
    (hA : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α)
    (hB : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α)
    (hRpos : 0 < R α) (hrpos : 0 < r α)
    (hsys : ∀ᶠ β in nhds α, R β ^ (2 * n + 2) + r β ^ (2 * n + 2) = 2 + A β ∧
      R β ^ (2 * n + 1) - r β ^ (2 * n + 1) = B β) :
    deriv R α
        = (((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α)
          / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) ∧
      deriv r α
        = (((2 * n + 1 : ℕ) : ℝ) * deriv A α - ((2 * n + 2 : ℕ) : ℝ) * R α * deriv B α)
          / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (R α + r α)) := by
  have hne : (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by simp
  have hRd : DifferentiableAt ℝ R α := hR.differentiableAt hne
  have hrd : DifferentiableAt ℝ r α := hr.differentiableAt hne
  have hAd : DifferentiableAt ℝ A α := hA.differentiableAt hne
  have hBd : DifferentiableAt ℝ B α := hB.differentiableAt hne
  -- Differentiate the first equation `R ^ (2n+2) + r ^ (2n+2) = 2 + A`.
  have hF_eq : (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2))) - A)
      =ᶠ[nhds α] (fun _ => (2 : ℝ)) := by
    filter_upwards [hsys] with β hβ
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith [hβ.1]
  have hF_deriv : deriv (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2))) - A) α
      = ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv R α
        + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv r α - deriv A α := by
    have h1 : DifferentiableAt ℝ (fun β => R β ^ (2 * n + 2)) α := hRd.fun_pow (2 * n + 2)
    have h2 : DifferentiableAt ℝ (fun β => r β ^ (2 * n + 2)) α := hrd.fun_pow (2 * n + 2)
    rw [deriv_sub (h1.add h2) hAd, deriv_add h1 h2,
      deriv_fun_pow hRd (2 * n + 2), deriv_fun_pow hrd (2 * n + 2)]
    simp only [show (2 * n + 2 - 1 : ℕ) = 2 * n + 1 from by omega]
  have hF_zero : deriv (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2))) - A) α
      = 0 :=
    (Filter.EventuallyEq.deriv_eq hF_eq).trans (deriv_const α 2)
  have hE1 : ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv R α
        + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv r α - deriv A α = 0 :=
    hF_deriv.symm.trans hF_zero
  -- Differentiate the second equation `R ^ (2n+1) - r ^ (2n+1) = B`.
  have hG_eq : (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B)
      =ᶠ[nhds α] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsys] with β hβ
    simp only [Pi.sub_apply]
    linarith [hβ.2]
  have hG_deriv : deriv (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B) α
      = ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α
        - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α - deriv B α := by
    have h1 : DifferentiableAt ℝ (fun β => R β ^ (2 * n + 1)) α := hRd.fun_pow (2 * n + 1)
    have h2 : DifferentiableAt ℝ (fun β => r β ^ (2 * n + 1)) α := hrd.fun_pow (2 * n + 1)
    rw [deriv_sub (h1.sub h2) hBd, deriv_sub h1 h2,
      deriv_fun_pow hRd (2 * n + 1), deriv_fun_pow hrd (2 * n + 1)]
    simp only [show (2 * n + 1 - 1 : ℕ) = 2 * n from by omega]
  have hG_zero : deriv (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B) α
      = 0 :=
    (Filter.EventuallyEq.deriv_eq hG_eq).trans (deriv_const α 0)
  have hE2 : ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α
        - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α - deriv B α = 0 :=
    hG_deriv.symm.trans hG_zero
  -- Rewrite the top powers so that everything is a polynomial in `R^2n`, `r^2n`, `R`, `r`.
  rw [pow_succ] at hE1
  have hR2n : R α ^ (2 * n) ≠ 0 := pow_ne_zero _ (ne_of_gt hRpos)
  have hr2n : r α ^ (2 * n) ≠ 0 := pow_ne_zero _ (ne_of_gt hrpos)
  have hsum : R α + r α ≠ 0 := ne_of_gt (by linarith)
  have hc1 : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc2 : ((2 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hden1 : ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc2 hc1) hR2n) hsum
  have hden2 : ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (R α + r α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc2 hc1) hr2n) hsum
  constructor
  · rw [eq_div_iff hden1]
    linear_combination ((2 * n + 1 : ℕ) : ℝ) * hE1 + (((2 * n + 2 : ℕ) : ℝ) * r α) * hE2
  · rw [eq_div_iff hden2]
    linear_combination ((2 * n + 1 : ℕ) : ℝ) * hE1 - (((2 * n + 2 : ℕ) : ℝ) * R α) * hE2

end Work.OddCurve.LowSlope
