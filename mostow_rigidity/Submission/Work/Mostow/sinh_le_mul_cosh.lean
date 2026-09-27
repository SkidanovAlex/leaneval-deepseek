import Mathlib

namespace Work.Mostow

theorem sinh_le_mul_cosh (x : ℝ) (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  -- `f t = t * cosh t - sinh t` has `f' t = t * sinh t ≥ 0` on `(0,∞)`, hence is
  -- monotone on `[0,∞)`; evaluating at `0` and `x` gives the claim.
  have hderiv : ∀ z : ℝ, deriv (fun t => t * Real.cosh t - Real.sinh t) z = z * Real.sinh z := by
    intro z
    conv_lhs =>
      arg 1
      rw [show (fun t : ℝ => t * Real.cosh t - Real.sinh t) = (id * Real.cosh) - Real.sinh
            from rfl]
    rw [deriv_sub (DifferentiableAt.mul differentiableAt_id Real.differentiableAt_cosh)
          Real.differentiableAt_sinh,
      deriv_mul differentiableAt_id Real.differentiableAt_cosh,
      deriv_id, Real.deriv_cosh, Real.deriv_sinh]
    show 1 * Real.cosh z + z * Real.sinh z - Real.cosh z = z * Real.sinh z
    ring
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro z hz
      rw [interior_Ici, Set.mem_Ioi] at hz
      rw [hderiv z]
      exact mul_nonneg (le_of_lt hz) (Real.sinh_nonneg_iff.mpr (le_of_lt hz))
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  have h2 : (0 : ℝ) ≤ x * Real.cosh x - Real.sinh x := by simpa using hmono h0 hx hx
  linarith

end Work.Mostow
