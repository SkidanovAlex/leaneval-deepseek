import Mathlib

namespace Work.FIArea2.SevenSix

open MeasureTheory Set

-- The one-dimensional substitution step of the FI (7.6) computation: for `h > 0`,
-- `∫₀^∞ f(ρ² h) dρ = (1/2) h^{-1/2} ∫₀^∞ f(u)/√u du` (substitute `u = ρ²h`).
-- Intended for arbitrary real `f` (the identity is unconditional for Bochner integrals).
theorem one_dim_scale (f : ℝ → ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ ρ in Set.Ioi 0, f (ρ ^ 2 * h)
      = (1 / 2) * h ^ (-(1 : ℝ) / 2) * ∫ u in Set.Ioi 0, f u / Real.sqrt u := by
  -- Step A: substitute `ρ = x ^ (1/2)` (i.e. `x = ρ²`), via `integral_comp_rpow_Ioi_of_pos`.
  have stepA : (∫ x in Ioi 0, ((1/2:ℝ) * x ^ ((1/2:ℝ) - 1)) • f ((x ^ ((1/2:ℝ))) ^ 2 * h))
      = ∫ ρ in Ioi 0, f (ρ ^ 2 * h) :=
    integral_comp_rpow_Ioi_of_pos (g := fun y => f (y ^ 2 * h)) (p := (1/2:ℝ)) (by norm_num)
  have stepA2 : (∫ x in Ioi 0, ((1/2:ℝ) * x ^ ((1/2:ℝ) - 1)) • f ((x ^ ((1/2:ℝ))) ^ 2 * h))
      = ∫ x in Ioi 0, (1/2) * x ^ (-(1:ℝ)/2) * f (x * h) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ((1/2:ℝ) * x ^ ((1/2:ℝ) - 1)) • f ((x ^ ((1/2:ℝ))) ^ 2 * h)
        = (1/2) * x ^ (-(1:ℝ)/2) * f (x * h)
    rw [smul_eq_mul]
    have hx2 : (x ^ ((1/2:ℝ))) ^ 2 = x := by rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
    rw [hx2, show (1/2:ℝ) - 1 = -(1:ℝ)/2 by norm_num]
  have hA : (∫ ρ in Ioi 0, f (ρ ^ 2 * h)) = ∫ x in Ioi 0, (1/2) * x ^ (-(1:ℝ)/2) * f (x * h) :=
    stepA.symm.trans stepA2
  -- Step B: substitute `x = u / h`, via `integral_comp_mul_left_Ioi`.
  have h2 : h ^ (1/2:ℝ) * h ^ (-(1:ℝ)/2) = 1 := by
    rw [← Real.rpow_add hh, show (1/2:ℝ) + (-(1:ℝ)/2) = 0 by norm_num, Real.rpow_zero]
  have key : ∫ x in Ioi 0, (1/2) * x ^ (-(1:ℝ)/2) * f (x * h)
      = h⁻¹ • ∫ y in Ioi 0, (1/2) * h ^ (1/2:ℝ) * y ^ (-(1:ℝ)/2) * f y := by
    have hcomp := integral_comp_mul_left_Ioi
      (fun y => (1/2:ℝ) * h ^ (1/2:ℝ) * y ^ (-(1:ℝ)/2) * f y) 0 hh
    simp only [mul_zero] at hcomp
    rw [← hcomp]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (1/2:ℝ) * x ^ (-(1:ℝ)/2) * f (x * h)
        = (1/2) * h ^ (1/2:ℝ) * (h * x) ^ (-(1:ℝ)/2) * f (h * x)
    rw [Real.mul_rpow hh.le hx.le, mul_comm h x]
    rw [show (1/2:ℝ) * h ^ (1/2:ℝ) * (h ^ (-(1:ℝ)/2) * x ^ (-(1:ℝ)/2)) * f (x * h)
          = (1/2:ℝ) * (h ^ (1/2:ℝ) * (h ^ (-(1:ℝ)/2) * x ^ (-(1:ℝ)/2))) * f (x * h) by ring]
    rw [show h ^ (1/2:ℝ) * (h ^ (-(1:ℝ)/2) * x ^ (-(1:ℝ)/2)) = x ^ (-(1:ℝ)/2) by
          rw [← mul_assoc, h2, one_mul]]
  -- Pull the constant `(1/2) h^{1/2}` out of the integral.
  have hconst : ∫ y in Ioi 0, (1/2) * h ^ (1/2:ℝ) * y ^ (-(1:ℝ)/2) * f y
      = ((1/2) * h ^ (1/2:ℝ)) * ∫ y in Ioi 0, y ^ (-(1:ℝ)/2) * f y := by
    rw [show (∫ y in Ioi 0, (1/2:ℝ) * h ^ (1/2:ℝ) * y ^ (-(1:ℝ)/2) * f y)
          = ∫ y in Ioi 0, ((1/2) * h ^ (1/2:ℝ)) * (y ^ (-(1:ℝ)/2) * f y) from
        setIntegral_congr_fun measurableSet_Ioi (fun y _ => by ring)]
    simpa only [smul_eq_mul] using
      (integral_smul ((1/2) * h ^ (1/2:ℝ)) (fun y => y ^ (-(1:ℝ)/2) * f y)
        (μ := volume.restrict (Ioi 0)))
  -- Rewrite `y ^ (-1/2) * f y` as `f y / sqrt y` on `Ioi 0`.
  have hsqrt : ∫ y in Ioi 0, y ^ (-(1:ℝ)/2) * f y = ∫ u in Ioi 0, f u / Real.sqrt u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    change z ^ (-(1:ℝ)/2) * f z = f z / Real.sqrt z
    rw [show (-(1:ℝ)/2 : ℝ) = -(1/2) by norm_num, Real.rpow_neg hz.le (1/2), ← Real.sqrt_eq_rpow,
        inv_mul_eq_div]
  -- Combine the constants `h⁻¹ * (1/2) h^{1/2} = (1/2) h^{-1/2}`.
  have hc : h⁻¹ * ((1/2:ℝ) * h ^ (1/2:ℝ)) = (1/2) * h ^ (-(1:ℝ)/2) := by
    rw [show h⁻¹ * ((1/2:ℝ) * h ^ (1/2:ℝ)) = (1/2) * (h⁻¹ * h ^ (1/2:ℝ)) by ring]
    rw [show h⁻¹ * h ^ (1/2:ℝ) = h ^ (-(1:ℝ)/2) by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hh]; congr 1; norm_num]
  have hfin : h⁻¹ • (((1/2) * h ^ (1/2:ℝ)) * ∫ u in Ioi 0, f u / Real.sqrt u)
      = (1/2) * h ^ (-(1:ℝ)/2) * ∫ u in Ioi 0, f u / Real.sqrt u := by
    rw [smul_eq_mul, ← mul_assoc, hc]
  calc (∫ ρ in Ioi 0, f (ρ ^ 2 * h))
      = ∫ x in Ioi 0, (1/2) * x ^ (-(1:ℝ)/2) * f (x * h) := hA
    _ = h⁻¹ • ∫ y in Ioi 0, (1/2) * h ^ (1/2:ℝ) * y ^ (-(1:ℝ)/2) * f y := key
    _ = h⁻¹ • (((1/2) * h ^ (1/2:ℝ)) * ∫ y in Ioi 0, y ^ (-(1:ℝ)/2) * f y) := by rw [hconst]
    _ = h⁻¹ • (((1/2) * h ^ (1/2:ℝ)) * ∫ u in Ioi 0, f u / Real.sqrt u) := by rw [hsqrt]
    _ = (1/2) * h ^ (-(1:ℝ)/2) * ∫ u in Ioi 0, f u / Real.sqrt u := hfin

end Work.FIArea2.SevenSix
