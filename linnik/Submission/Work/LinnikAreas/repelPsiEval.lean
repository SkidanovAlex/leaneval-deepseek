import Mathlib
import Submission.Work.LinnikAreas.RepelDefs

namespace Work.LinnikAreas

/-- Rescaling (`t = x s`) of the Laplace transform of the triangle of length `x`:
`∫₀ˣ e^{a t} (x - t) dt = x² Ψ(a x)`.  For `x = 0` both sides vanish; for `x > 0` it is the
substitution `t = x s` together with `x - x s = x (1 - s)`. -/
theorem repelPsiEval (x a : ℝ) (hx : 0 ≤ x) :
    ∫ t in (0:ℝ)..x, Real.exp (a * t) * (x - t) = x ^ 2 * repelPsi (a * x) := by
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · subst h0
    simp
  have hxne : x ≠ 0 := ne_of_gt hxpos
  rw [repelPsi]
  set I := ∫ t in (0:ℝ)..x, Real.exp (a * t) * (x - t) with hI
  set P := ∫ t in (0:ℝ)..1, Real.exp ((a * x) * t) * (1 - t) with hP
  -- substitution `t = x s` on `[0, 1]`
  have hsub : (∫ s in (0:ℝ)..1, Real.exp (a * (x * s)) * (x - x * s)) = x⁻¹ * I := by
    have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
      (f := fun t => Real.exp (a * t) * (x - t)) hxne
    simpa [hI] using h
  -- the substituted integrand is `x` times the `repelPsi` integrand `e^{(ax)s}(1-s)`
  have hval : (∫ s in (0:ℝ)..1, Real.exp (a * (x * s)) * (x - x * s)) = x * P := by
    rw [hP]
    rw [show (∫ s in (0:ℝ)..1, Real.exp (a * (x * s)) * (x - x * s))
        = ∫ s in (0:ℝ)..1, x * (Real.exp ((a * x) * s) * (1 - s)) from
      intervalIntegral.integral_congr (fun s _ => by
        rw [show a * (x * s) = (a * x) * s by ring]; ring)]
    rw [intervalIntegral.integral_const_mul]
  have hEq : x⁻¹ * I = x * P := hsub.symm.trans hval
  calc I = 1 * I := (one_mul I).symm
    _ = (x * x⁻¹) * I := by rw [mul_inv_cancel₀ hxne]
    _ = x * (x⁻¹ * I) := by ring
    _ = x * (x * P) := by rw [hEq]
    _ = x ^ 2 * P := by ring

end Work.LinnikAreas
