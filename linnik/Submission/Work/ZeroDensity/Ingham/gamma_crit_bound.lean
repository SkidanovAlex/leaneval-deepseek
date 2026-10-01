import Mathlib
import Submission.Work.ZeroDensity.Ingham.CritCommons

namespace Work.ZeroDensity.Ingham

/-- Explicit exponential-decay bound for `Γ` on the strip `-1/2 ≤ Re ≤ 1/2` with `|Im| ≥ 1`.
Write `z = u + iv`, `u ∈ [-1/2,1/2]`, `|v| ≥ 1`.  If `0 < u` apply
`Commons.Analysis.Complex.gamma_strip_upper` directly at `(u,v)`.  If `u ≤ 0`, use
`Complex.Gamma_add_one` (`Γ(z) = Γ(z+1)/z` for `z ≠ 0`, and `z ≠ 0` since `|v| ≥ 1`) so that
`‖Γ z‖ = ‖Γ (z+1)‖ / ‖z‖ ≤ ‖Γ (z+1)‖` (as `‖z‖ ≥ |v| ≥ 1`), and then `gamma_strip_upper` at
`u+1 ∈ [1/2, 3/2]`, giving `K6 (1+|v|)^6 exp(-(π/2)|v|)` in both cases. -/
theorem gamma_crit_bound (z : ℂ) (hlo : -(1 / 2 : ℝ) ≤ z.re) (hhi : z.re ≤ 1 / 2)
    (him : 1 ≤ |z.im|) :
    ‖Complex.Gamma z‖ ≤ Commons.Analysis.Complex.K6 * (1 + |z.im|) ^ (6 : ℝ)
      * Real.exp (-(Real.pi / 2) * |z.im|) := by
  have hdec : z = ((z.re : ℂ) + Complex.I * (z.im : ℂ)) := by
    apply Complex.ext <;> simp
  by_cases hpos : 0 < z.re
  · -- Right half of the critical strip: apply the vertical-strip bound directly.
    have hz := Commons.Analysis.Complex.gamma_strip_upper z.re z.im hpos (by linarith) him
    have hGam : Complex.Gamma z = Complex.Gamma ((z.re : ℂ) + Complex.I * (z.im : ℂ)) :=
      congrArg Complex.Gamma hdec
    rw [hGam]
    exact hz
  · -- Left half: shift by one via `Γ(z+1) = z·Γ(z)`.
    rw [not_lt] at hpos
    have hne : z ≠ 0 := by
      intro h0
      have hz0 : z.im = 0 := by rw [h0]; simp
      rw [hz0, abs_zero] at him
      linarith
    have hshift := Complex.Gamma_add_one z hne
    have hnorm1 : (1 : ℝ) ≤ ‖z‖ := by
      calc (1 : ℝ) ≤ |z.im| := him
        _ ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hrel : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 1)‖ := by
      calc ‖Complex.Gamma z‖ ≤ ‖z‖ * ‖Complex.Gamma z‖ :=
            le_mul_of_one_le_left (norm_nonneg _) hnorm1
        _ = ‖z * Complex.Gamma z‖ := by rw [norm_mul]
        _ = ‖Complex.Gamma (z + 1)‖ := by rw [hshift]
    have hz1 : z + 1 = (((z.re + 1 : ℝ) : ℂ) + Complex.I * (z.im : ℂ)) := by
      apply Complex.ext <;> simp
    have hz2 := Commons.Analysis.Complex.gamma_strip_upper (z.re + 1) z.im
      (by linarith) (by linarith) him
    calc ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 1)‖ := hrel
      _ = ‖Complex.Gamma (((z.re + 1 : ℝ) : ℂ) + Complex.I * (z.im : ℂ))‖ := by rw [hz1]
      _ ≤ Commons.Analysis.Complex.K6 * (1 + |z.im|) ^ (6 : ℝ) *
            Real.exp (-(Real.pi / 2) * |z.im|) := hz2

end Work.ZeroDensity.Ingham
