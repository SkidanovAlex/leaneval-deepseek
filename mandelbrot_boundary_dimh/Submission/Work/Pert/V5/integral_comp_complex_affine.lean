import Mathlib

namespace Work.Pert.V5

theorem integral_comp_complex_affine {α : ℂ} (hα : α ≠ 0) {s a b : ℝ} (hab : a ≤ b) (f : ℂ → ℝ) :
    ∫ x in a..b, f (α * ((x : ℂ) + (s : ℂ) * Complex.I))
      = (1 / ‖α‖) * ∫ t in (0 : ℝ)..(‖α‖ * (b - a)),
          f (α * ((a : ℂ) + (s : ℂ) * Complex.I) + (t : ℂ) * (α / ‖α‖)) := by
  -- The point of the statement: `x ↦ α * ((x : ℂ) + s * I)` restricted to `[a,b]` is the
  -- arclength parametrisation of a segment (the factor `α / ‖α‖` has modulus one, so the
  -- derivative has modulus `‖α‖`), hence reparametrising `x = a + t / ‖α‖` multiplies the
  -- integral by the inverse of that speed.
  have hαn : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα
  -- Reparametrised integrand, already written through the image point `α * (a + s*I)`.
  set g : ℝ → ℝ := fun t => f (α * ((a : ℂ) + (s : ℂ) * Complex.I) + (t : ℂ) * (α / ‖α‖))
    with hg
  -- The two affine expressions agree pointwise on the segment.
  have key : ∀ x : ℝ, f (α * ((x : ℂ) + (s : ℂ) * Complex.I)) = g (‖α‖ * x - ‖α‖ * a) := by
    intro x
    simp only [hg]
    congr 1
    have hc : ((‖α‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hαn
    -- `(‖α‖ * x - ‖α‖ * a) * (α / ‖α‖) = (x - a) * α`, since `α = ‖α‖ * (α / ‖α‖)`.
    have h2 : (((‖α‖ * x - ‖α‖ * a : ℝ)) : ℂ) * (α / ‖α‖) = α * ((x - a : ℝ) : ℂ) := by
      rw [div_eq_mul_inv]
      push_cast
      field_simp
    rw [h2]
    push_cast
    ring
  rw [show (∫ x in a..b, f (α * ((x : ℂ) + (s : ℂ) * Complex.I)))
        = ∫ x in a..b, g (‖α‖ * x - ‖α‖ * a) from by
      apply intervalIntegral.integral_congr
      intro x _
      exact key x]
  -- Now apply the affine substitution `x ↦ ‖α‖ * x - ‖α‖ * a`.
  rw [intervalIntegral.integral_comp_mul_sub g hαn]
  rw [show ‖α‖ * a - ‖α‖ * a = (0 : ℝ) from by ring,
      show ‖α‖ * b - ‖α‖ * a = ‖α‖ * (b - a) from by ring]
  rw [smul_eq_mul, inv_eq_one_div]

end Work.Pert.V5
