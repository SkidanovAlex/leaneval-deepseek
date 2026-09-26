import Mathlib
import Submission.Work.RadialSpace.EvenHalfDeriv

namespace Work.RadialSpace

/-- The derivative at `0` of an even function vanishes. -/
private lemma deriv_zero_of_even {g : ℝ → ℂ} (he : Function.Even g) : deriv g 0 = 0 := by
  have h : (fun x : ℝ => g (-x)) = g := funext he
  have hcomp : deriv (fun x : ℝ => g (-x)) 0 = deriv g 0 := by rw [h]
  rw [deriv_comp_neg] at hcomp
  simp only [neg_zero] at hcomp
  have h2 : deriv g 0 = -deriv g 0 := hcomp.symm
  have h5 : deriv g 0 + deriv g 0 = 0 := by
    nth_rewrite 1 [h2]; exact neg_add_cancel _
  have h6 : (2 : ℂ) * deriv g 0 = 0 := by rw [two_mul]; exact h5
  exact (mul_eq_zero.mp h6).resolve_left two_ne_zero

theorem evenHalfDeriv_eq {g : ℝ → ℂ} (hg : ContDiff ℝ Work.RadialSpace.Smooth g) (he : Function.Even g)
    {u : ℝ} (hu : u ≠ 0) : Work.RadialSpace.evenHalfDeriv g u = deriv g u / (2 * u) := by
  -- The second derivative, written as the derivative of `deriv g`.
  have hinner2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- `deriv g` is differentiable and `iteratedDeriv 2 g` is continuous.
  have hdiffd : Differentiable ℝ (deriv g) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg).2).1
  have hcont : Continuous (iteratedDeriv 2 g) := by
    rw [hinner2]
    exact ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg).2).2).continuous
  -- Fundamental theorem of calculus: `∫_0^u g'' = g'(u) - g'(0)`.
  have hFTC : ∫ s in (0:ℝ)..u, iteratedDeriv 2 g s = deriv g u - deriv g 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [hinner2]
      exact (hdiffd x).hasDerivAt
    · exact hcont.intervalIntegrable 0 u
  -- Change of variables in the defining integral.
  have hsub : ∫ t in (0:ℝ)..1, iteratedDeriv 2 g (u * t)
      = u⁻¹ • ∫ s in (0:ℝ)..u, iteratedDeriv 2 g s := by
    rw [show (fun t : ℝ => iteratedDeriv 2 g (u * t))
          = (fun t : ℝ => iteratedDeriv 2 g (t * u)) from by
        funext t; rw [mul_comm]]
    rw [intervalIntegral.integral_comp_mul_right (fun s : ℝ => iteratedDeriv 2 g s) hu]
    simp
  rw [evenHalfDeriv_apply, hsub, hFTC, deriv_zero_of_even he, sub_zero]
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [Algebra.smul_def]
  push_cast
  field_simp
  ring_nf
  simp [mul_assoc, mul_inv_cancel₀ hu']

end Work.RadialSpace
