import Mathlib

/-! Helpers: iterated derivatives of `t ↦ exp (c * t^2 / 2)` at 0. -/

noncomputable section
open scoped BigOperators

namespace Submission.Discrepancy

private def E (c : ℝ) : ℝ → ℝ := fun t => Real.exp (c * t ^ 2 / 2)

lemma deriv_sq (t : ℝ) : deriv (fun u : ℝ => u ^ 2) t = 2 * t := by
  simp

lemma deriv_cb (t : ℝ) : deriv (fun u : ℝ => u ^ 3) t = 3 * t ^ 2 := by
  simp

lemma deriv_cid (c t : ℝ) : deriv (fun u : ℝ => c * u) t = c := by
  simp

/-- The first derivative of `t ↦ exp (c t²/2)`. -/
lemma deriv_E (c t : ℝ) : deriv (E c) t = c * t * E c t := by
  unfold E
  rw [deriv_exp (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => c * u ^ 2 / 2) t)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, DifferentiableAt.fun_pow,
    deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow, pow_one, deriv_id'', mul_one, zero_add]
  ring

lemma deriv_poly1 (c t : ℝ) : deriv (fun u : ℝ => c + c ^ 2 * u ^ 2) t = 2 * c ^ 2 * t := by
  change deriv ((fun _ : ℝ => c) + (fun u : ℝ => c ^ 2 * u ^ 2)) t = 2 * c ^ 2 * t
  rw [deriv_add (by fun_prop) (by fun_prop)]
  simp
  ring

lemma deriv_poly2 (c t : ℝ) : deriv (fun u : ℝ => 3 * c ^ 2 * u + c ^ 3 * u ^ 3) t =
    3 * c ^ 2 + 3 * c ^ 3 * t ^ 2 := by
  change deriv ((fun u : ℝ => 3 * c ^ 2 * u) + (fun u : ℝ => c ^ 3 * u ^ 3)) t =
    3 * c ^ 2 + 3 * c ^ 3 * t ^ 2
  rw [deriv_add (by fun_prop) (by fun_prop)]
  simp
  ring

lemma deriv_lin (c t : ℝ) : deriv (fun u : ℝ => c * u * E c u) t = (c + c ^ 2 * t ^ 2) * E c t := by
  rw [deriv_fun_mul (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => c * u) t)
    (by unfold E; fun_prop : DifferentiableAt ℝ (fun u : ℝ => E c u) t)]
  rw [deriv_cid, deriv_E]
  ring

lemma deriv_quad (c t : ℝ) : deriv (fun u : ℝ => (c + c ^ 2 * u ^ 2) * E c u) t =
    (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * E c t := by
  rw [deriv_fun_mul (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => c + c ^ 2 * u ^ 2) t)
    (by unfold E; fun_prop : DifferentiableAt ℝ (fun u : ℝ => E c u) t)]
  rw [deriv_poly1, deriv_E]
  ring

lemma deriv_cubic (c t : ℝ) : deriv (fun u : ℝ => (3 * c ^ 2 * u + c ^ 3 * u ^ 3) * E c u) t =
    (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * E c t := by
  rw [deriv_fun_mul (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => 3 * c ^ 2 * u + c ^ 3 * u ^ 3) t)
    (by unfold E; fun_prop : DifferentiableAt ℝ (fun u : ℝ => E c u) t)]
  rw [deriv_poly2, deriv_E]
  ring

/-- `iteratedDeriv 1 (t ↦ exp (c t²/2)) t = c t e` -/
lemma iterDeriv1_E (c t : ℝ) : iteratedDeriv 1 (E c) t = c * t * E c t := by
  rw [iteratedDeriv_one]
  exact deriv_E c t

/-- `iteratedDeriv 2 (t ↦ exp (c t²/2)) t = (c + c²t²) e` -/
lemma iterDeriv2_E (c t : ℝ) : iteratedDeriv 2 (E c) t = (c + c ^ 2 * t ^ 2) * E c t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (E c) = fun u : ℝ => c * u * E c u by
    funext u; rw [deriv_E]]
  exact deriv_lin c t

/-- `iteratedDeriv 3 (t ↦ exp (c t²/2)) t = (3c²t + c³t³) e` -/
lemma iterDeriv3_E (c t : ℝ) : iteratedDeriv 3 (E c) t = (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * E c t := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (E c) = fun u : ℝ => c * u * E c u by
    funext u; rw [deriv_E]]
  rw [show deriv (fun v : ℝ => c * v * E c v) = fun u : ℝ => (c + c ^ 2 * u ^ 2) * E c u by
    funext u; rw [deriv_lin]]
  exact deriv_quad c t

/-- `iteratedDeriv 4 (t ↦ exp (c t²/2)) t = (3c² + 6c³t² + c⁴t⁴) e` -/
lemma iterDeriv4_E (c t : ℝ) : iteratedDeriv 4 (E c) t =
    (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * E c t := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (E c) = fun u : ℝ => c * u * E c u by
    funext u; rw [deriv_E]]
  rw [show deriv (fun v : ℝ => c * v * E c v) = fun u : ℝ => (c + c ^ 2 * u ^ 2) * E c u by
    funext u; rw [deriv_lin]]
  rw [show deriv (fun v : ℝ => (c + c ^ 2 * v ^ 2) * E c v) =
      fun u : ℝ => (3 * c ^ 2 * u + c ^ 3 * u ^ 3) * E c u by
    funext u; rw [deriv_quad]]
  exact deriv_cubic c t

/-- `iteratedDeriv 1 (t ↦ exp (c t²/2)) 0 = 0` -/
lemma iter1_eqf_zero (c : ℝ) : iteratedDeriv 1 (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0 = 0 := by
  change iteratedDeriv 1 (E c) 0 = 0
  rw [iterDeriv1_E]
  norm_num [E, Real.exp_zero]

/-- `iteratedDeriv 2 (t ↦ exp (c t²/2)) 0 = c` -/
lemma iter2_eqf_zero (c : ℝ) : iteratedDeriv 2 (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0 = c := by
  change iteratedDeriv 2 (E c) 0 = c
  rw [iterDeriv2_E]
  norm_num [E, Real.exp_zero]

/-- `iteratedDeriv 3 (t ↦ exp (c t²/2)) 0 = 0` -/
lemma iter3_eqf_zero (c : ℝ) : iteratedDeriv 3 (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0 = 0 := by
  change iteratedDeriv 3 (E c) 0 = 0
  rw [iterDeriv3_E]
  norm_num [E, Real.exp_zero]

/-- `iteratedDeriv 4 (t ↦ exp (c t²/2)) 0 = 3 c²` -/
lemma iter4_eqf_zero (c : ℝ) : iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0 = 3 * c ^ 2 := by
  change iteratedDeriv 4 (E c) 0 = 3 * c ^ 2
  rw [iterDeriv4_E]
  norm_num [E, Real.exp_zero]

end Discrepancy
