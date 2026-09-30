import Mathlib
import Submission.Work.BMF.exp_cube_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bound for `∫₀^∞ exp (η x log 2 - (x log 2)³ / (D L²)) dx`

We prove, for `D, L > 0` and `η ≥ 0`,

`∫₀^∞ exp (η x log 2 - (x log 2)³ / (D L²)) dx
    ≤ (4 / log 2) · D^{1/3} · L^{2/3} · exp ((2/9) √(3D) η^{3/2} L)`.

The proof is a two-step change of variables.  First `t = x log 2` turns the integral into
`(log 2)⁻¹ ∫₀^∞ exp (η t - b t³) dt` with `b = 1/(D L²)`; then `u = b^{1/3} t` removes `b`:

`∫₀^∞ exp (η t - b t³) dt = b^{-1/3} ∫₀^∞ exp (A u - u³) du`,  `A = η b^{-1/3}`.

The remaining integral is the sharp saddle-point estimate
`∫₀^∞ exp (A u - u³) du ≤ 4 exp ((2/(3√3)) A^{3/2})`, obtained from
`Work.BMF.exp_cube_integral_le` (stated there with `A = 3y²`).
-/

namespace Work.BMF

open MeasureTheory

/-- General saddle-point bound.  For `A ≥ 0` and `b > 0`,

`∫₀^∞ exp (A t - b t³) dt ≤ 4 b^{-1/3} exp ((2/(3√3)) A^{3/2} b^{-1/2})`.

The substitution `t = b^{-1/3} u` reduces this to
`∫₀^∞ exp (A b^{-1/3} u - u³) du ≤ 4 exp (2 y³)` with `y = √(A b^{-1/3}/3)`, which is
`exp_cube_integral_le`. -/
lemma int_exp_quad_cube_le (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) :
    ∫ t in Set.Ioi (0:ℝ), Real.exp (A * t - b * t^3) ≤
      4 * b ^ (-(1/3) : ℝ) *
        Real.exp ((2/(3*Real.sqrt 3)) * A ^ (3/2:ℝ) * b ^ (-(1/2):ℝ)) := by
  have hb0 : 0 ≤ b := le_of_lt hb
  have hb13pos : 0 < b ^ (1/3:ℝ) := Real.rpow_pos_of_pos hb _
  set y : ℝ := Real.sqrt (A/(3 * b^(1/3:ℝ))) with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = A/(3*b^(1/3:ℝ)) := by rw [hy]; exact Real.sq_sqrt (by positivity)
  have hy2r : y^(2:ℝ) = A/(3*b^(1/3:ℝ)) := by rw [Real.rpow_two]; exact hy2
  have h3y2 : 3 * y^2 = A * b^(-(1/3):ℝ) := by rw [hy2, Real.rpow_neg hb0]; field_simp
  have hpt : ∀ x : ℝ, Real.exp (A * x - b * x^3) =
      Real.exp (3 * y^2 * (b^(1/3:ℝ) * x) - (b^(1/3:ℝ) * x)^3) := by
    intro x
    congr 1
    rw [h3y2]
    have h1 : A * b^(-(1/3):ℝ) * (b^(1/3:ℝ) * x) = A * x := by
      rw [show A * b^(-(1/3):ℝ) * (b^(1/3:ℝ) * x)
            = A * (b^(-(1/3):ℝ) * b^(1/3:ℝ)) * x by ring]
      rw [show b^(-(1/3):ℝ) * b^(1/3:ℝ) = 1 by rw [← Real.rpow_add hb]; norm_num]
      ring
    have h2 : (b^(1/3:ℝ) * x)^3 = b * x^3 := by
      rw [mul_pow, show (b^(1/3:ℝ))^3 = b by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]; norm_num]
    rw [h1, h2]
  have hEq : (∫ t in Set.Ioi (0:ℝ), Real.exp (A*t - b*t^3)) =
      ∫ x in Set.Ioi (0:ℝ), Real.exp (3*y^2*(b^(1/3:ℝ)*x) - (b^(1/3:ℝ)*x)^3) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact hpt x
  rw [hEq]
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (g := fun u => Real.exp (3*y^2*u - u^3)) 0 hb13pos
  rw [hsub]
  simp only [mul_zero]
  rw [smul_eq_mul]
  have hkey := exp_cube_integral_le y hy0
  have hy3 : 2*y^3 = (2/(3*Real.sqrt 3)) * A^(3/2:ℝ) * b^(-(1/2):ℝ) := by
    have hy3pow : y^3 = (y^(2:ℝ))^(3/2:ℝ) := by
      rw [← Real.rpow_natCast y 3, ← Real.rpow_mul hy0 (2:ℝ) (3/2:ℝ)]; norm_num
    rw [hy3pow, hy2r, Real.div_rpow hA (by positivity),
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (Real.rpow_nonneg hb0 _)]
    have h3 : (3:ℝ)^(3/2:ℝ) = 3 * Real.sqrt 3 := by
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 3),
        Real.rpow_one, Real.sqrt_eq_rpow]
    have hb' : (b^(1/3:ℝ))^(3/2:ℝ) = b^(1/2:ℝ) := by
      rw [← Real.rpow_mul hb0]; norm_num
    rw [h3, hb', Real.rpow_neg hb0]
    field_simp
  calc (b^(1/3:ℝ))⁻¹ * ∫ u in Set.Ioi (0:ℝ), Real.exp (3*y^2*u - u^3)
      ≤ (b^(1/3:ℝ))⁻¹ * (4 * Real.exp (2*y^3)) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hb13pos.le)
    _ = 4 * b^(-(1/3):ℝ) *
          Real.exp ((2/(3*Real.sqrt 3)) * A^(3/2:ℝ) * b^(-(1/2):ℝ)) := by
        rw [show (b^(1/3:ℝ))⁻¹ = b^(-(1/3):ℝ) by rw [Real.rpow_neg hb0], hy3]
        ring

/-- Prefactor/exponent identity relating the `b = 1/(D L²)` normalisation to `D, L`. -/
lemma cube_integral_rpow_match (D L η : ℝ) (hD : 0 < D) (hL : 0 < L) (_hη : 0 ≤ η) :
    (4 / Real.log 2) * (1 / (D * L ^ 2)) ^ (-(1 / 3) : ℝ) *
        Real.exp ((2 / (3 * Real.sqrt 3)) * η ^ (3 / 2 : ℝ) *
          (1 / (D * L ^ 2)) ^ (-(1 / 2) : ℝ))
      = (4 / Real.log 2) * D ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) *
        Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L) := by
  have hDL : 0 < D * L^2 := by positivity
  have hb13 : (1/(D*L^2))^(-(1/3):ℝ) = D^(1/3:ℝ) * L^(2/3:ℝ) := by
    rw [one_div, Real.inv_rpow (le_of_lt hDL), Real.rpow_neg (le_of_lt hDL) (1/3:ℝ), inv_inv]
    rw [Real.mul_rpow (le_of_lt hD) (by positivity : (0:ℝ) ≤ L^2)]
    congr 1
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul (le_of_lt hL)]
    norm_num
  have hb12 : (1/(D*L^2))^(-(1/2):ℝ) = Real.sqrt D * L := by
    rw [one_div, Real.inv_rpow (le_of_lt hDL), Real.rpow_neg (le_of_lt hDL) (1/2:ℝ), inv_inv]
    rw [Real.mul_rpow (le_of_lt hD) (by positivity : (0:ℝ) ≤ L^2), Real.sqrt_eq_rpow]
    congr 1
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul (le_of_lt hL)]
    norm_num
  have hsc' : 2/(3*Real.sqrt 3) = (2/9)*Real.sqrt 3 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith [h3]
  have hsc : (2/(3*Real.sqrt 3)) * Real.sqrt D = (2/9) * Real.sqrt (3*D) := by
    rw [hsc', Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3) D]
    ring
  have harg : (2/(3*Real.sqrt 3)) * η^(3/2:ℝ) * (Real.sqrt D * L)
      = (2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L := by
    rw [show (2/(3*Real.sqrt 3)) * η^(3/2:ℝ) * (Real.sqrt D * L)
          = ((2/(3*Real.sqrt 3))*Real.sqrt D) * η^(3/2:ℝ) * L by ring, hsc]
  rw [hb13, hb12, harg]
  ring

theorem int_exp_cube_le (D L η : ℝ) (hD : 0 < D) (hL : 0 < L) (hη : 0 ≤ η) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (η * x * Real.log 2 - (x * Real.log 2) ^ 3 / (D * L ^ 2)) ≤
      (4 / Real.log 2) * D ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) *
        Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L) := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set b : ℝ := 1/(D*L^2) with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  -- pointwise rewrite of the integrand into the `b`-normalised form
  have hpt : ∀ x : ℝ,
      Real.exp (η * x * Real.log 2 - (x * Real.log 2) ^ 3 / (D * L^2))
        = Real.exp (η * (Real.log 2 * x) - b * (Real.log 2 * x)^3) := by
    intro x
    congr 1
    rw [hbdef, div_eq_mul_inv]
    ring
  have hEq : (∫ x in Set.Ioi (0:ℝ),
        Real.exp (η * x * Real.log 2 - (x * Real.log 2)^3 / (D*L^2)))
      = ∫ x in Set.Ioi (0:ℝ), Real.exp (η * (Real.log 2 * x) - b * (Real.log 2 * x)^3) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact hpt x
  rw [hEq]
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (g := fun t => Real.exp (η*t - b*t^3)) 0 hc
  simp only [mul_zero] at hsub
  rw [hsub, smul_eq_mul]
  have hkey := int_exp_quad_cube_le η b hη hb
  calc (Real.log 2)⁻¹ * ∫ t in Set.Ioi (0:ℝ), Real.exp (η * t - b * t^3)
      ≤ (Real.log 2)⁻¹ * (4 * b^(-(1/3):ℝ) *
          Real.exp ((2/(3*Real.sqrt 3)) * η^(3/2:ℝ) * b^(-(1/2):ℝ))) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hc.le)
    _ = (4 / Real.log 2) * D ^ (1/3:ℝ) * L ^ (2/3:ℝ) *
          Real.exp ((2/9) * Real.sqrt (3*D) * η^(3/2:ℝ) * L) := by
        rw [show (Real.log 2)⁻¹ * (4 * b^(-(1/3):ℝ) *
              Real.exp ((2/(3*Real.sqrt 3)) * η^(3/2:ℝ) * b^(-(1/2):ℝ)))
              = (4 / Real.log 2) * b^(-(1/3):ℝ) *
                Real.exp ((2/(3*Real.sqrt 3)) * η^(3/2:ℝ) * b^(-(1/2):ℝ)) by ring,
            hbdef]
        exact cube_integral_rpow_match D L η hD hL hη

end Work.BMF
