import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

open MeasureTheory Real Set

/-- The real-valued radial moment: `∫₀^∞ r ^ (2 n + 1) e ^ (- r ^ 2) dr = n ! / 2`.

This is the substitution `u = r ^ 2` applied to the Gamma integral
`∫₀^∞ u ^ n e ^ (-u) du = n !`. -/
theorem real_radialMoment (n : ℕ) :
    ∫ r : ℝ in Set.Ioi 0, r ^ (2 * n + 1) * Real.exp (-(r ^ 2)) = (n.factorial : ℝ) / 2 := by
  -- `∫₀^∞ y ^ n e ^ (-y) dy = n !`
  have hgamma : ∫ y : ℝ in Set.Ioi 0, y ^ n * Real.exp (-y) = (n.factorial : ℝ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1)
      (by positivity) one_pos
    simp only [one_mul] at h
    rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring] at h
    simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h
  -- change of variables `x ↦ x ^ 2` in the integral over `Ioi 0`
  have hkey := integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ n * Real.exp (-y))
    (p := 2) (by norm_num)
  have hkey' : ∫ x : ℝ in Set.Ioi 0,
        (2 * x ^ ((2 : ℝ) - 1)) • ((x ^ (2 : ℝ)) ^ n * Real.exp (-(x ^ (2 : ℝ))))
      = (n.factorial : ℝ) := hkey.trans hgamma
  have h2 : ∫ x : ℝ in Set.Ioi 0, 2 * (x ^ (2 * n + 1) * Real.exp (-(x ^ 2)))
      = (n.factorial : ℝ) := by
    rw [← hkey']
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [smul_eq_mul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_ofNat, ← pow_mul, pow_succ]
    ring
  rw [integral_const_mul] at h2
  linarith

theorem radialMoment (n : ℕ) :
    ∫ r : ℝ in Set.Ioi 0, (r : ℂ) ^ (2 * n + 1) * Complex.exp (-(r : ℂ) ^ 2)
      = (n.factorial : ℂ) / 2 := by
  -- transfer the complex integral to the real one
  have hB : (∫ r : ℝ in Set.Ioi 0, ((r ^ (2 * n + 1) * Real.exp (-(r ^ 2)) : ℝ) : ℂ))
      = ((∫ r : ℝ in Set.Ioi 0, r ^ (2 * n + 1) * Real.exp (-(r ^ 2)) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ) (f := fun r : ℝ => r ^ (2 * n + 1) * Real.exp (-(r ^ 2)))
      (μ := volume.restrict (Set.Ioi 0))
  have htrans : ∫ r : ℝ in Set.Ioi 0, (r : ℂ) ^ (2 * n + 1) * Complex.exp (-(r : ℂ) ^ 2)
      = ((∫ r : ℝ in Set.Ioi 0, r ^ (2 * n + 1) * Real.exp (-(r ^ 2)) : ℝ) : ℂ) :=
    (setIntegral_congr_fun measurableSet_Ioi (fun r _ => by
      push_cast [Complex.ofReal_exp]; ring)).trans hB
  rw [htrans, real_radialMoment n]
  push_cast
  ring

end Work.BoseB4
