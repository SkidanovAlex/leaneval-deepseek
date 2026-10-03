import Mathlib

namespace Work.FIArea2.SevenSix

open MeasureTheory Set

-- The two substitutions `t₁ = √r`, `t₂ = √s` in the FI (7.6) quadrant integral,
-- `dt₁ dt₂ = dr ds / (4 √r √s)`. Intended for arbitrary real `f` (unconditional identity).
-- Route: apply `MeasureTheory.integral_comp_rpow_Ioi_of_pos` with `p = 1/2` twice, once to the
-- inner integral (with `g := fun y => f (t₁^4 - 2*γ*t₁^2*y^2 + y^4)`) and once to the outer one
-- (with `g := fun y => ∫ s, s^(-1/2) * f (y^4 - 2*γ*y^2*s + s^2)`), using `(y^(1/2))^2 = y`
-- and `(y^(1/2))^4 = y^2` for `y ≥ 0`, then combining constants and rewriting
-- `r^(-1/2) * s^(-1/2) = 1/√(r*s)`.
theorem quadrant_double_eq (f : ℝ → ℝ) (γ : ℝ) :
    ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0, f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      = (1 / 4) * ∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s) := by
  -- Inner substitution `t₂ = √s`, i.e. `s = t₂²`.
  have hinner : ∀ t₁ : ℝ,
      ∫ t₂ in Set.Ioi 0, f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4)
        = ∫ s in Set.Ioi 0,
            (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * s + s ^ 2) := by
    intro t₁
    have h := MeasureTheory.integral_comp_rpow_Ioi_of_pos
      (g := fun y => f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * y ^ 2 + y ^ 4))
      (p := (1 / 2 : ℝ)) (by norm_num)
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul]
    have hx1 : (x ^ ((1 / 2 : ℝ))) ^ 2 = x := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
    have hx4 : (x ^ ((1 / 2 : ℝ))) ^ 4 = x ^ 2 := by
      rw [show (x ^ ((1 / 2 : ℝ))) ^ 4 = ((x ^ ((1 / 2 : ℝ))) ^ 2) ^ 2 by ring, hx1]
    rw [hx4, hx1, show (1 / 2 : ℝ) - 1 = -(1 : ℝ) / 2 by norm_num]
  -- Apply the inner identity under the outer integral.
  have h1 : (∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
        f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4))
      = ∫ t₁ in Set.Ioi 0, ∫ s in Set.Ioi 0,
          (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * s + s ^ 2) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t₁ _
    simp only []
    exact hinner t₁
  -- Outer substitution `t₁ = √r`, i.e. `r = t₁²`.
  have h2 : (∫ t₁ in Set.Ioi 0, ∫ s in Set.Ioi 0,
        (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * s + s ^ 2))
      = ∫ r in Set.Ioi 0, (1 / 2) * r ^ (-(1 : ℝ) / 2) *
          (∫ s in Set.Ioi 0,
            (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (r ^ 2 - 2 * γ * r * s + s ^ 2)) := by
    have h := MeasureTheory.integral_comp_rpow_Ioi_of_pos
      (g := fun y => ∫ s in Set.Ioi 0,
        (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (y ^ 4 - 2 * γ * y ^ 2 * s + s ^ 2))
      (p := (1 / 2 : ℝ)) (by norm_num)
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul]
    have hx1 : (x ^ ((1 / 2 : ℝ))) ^ 2 = x := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
    have hx4 : (x ^ ((1 / 2 : ℝ))) ^ 4 = x ^ 2 := by
      rw [show (x ^ ((1 / 2 : ℝ))) ^ 4 = ((x ^ ((1 / 2 : ℝ))) ^ 2) ^ 2 by ring, hx1]
    rw [hx4, hx1, show (1 / 2 : ℝ) - 1 = -(1 : ℝ) / 2 by norm_num]
  -- Move the outer weight inside the inner integral and combine constants.
  have h3 : (∫ r in Set.Ioi 0, (1 / 2) * r ^ (-(1 : ℝ) / 2) *
          (∫ s in Set.Ioi 0,
            (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (r ^ 2 - 2 * γ * r * s + s ^ 2)))
      = ∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          (1 / 4) * (f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only []
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hrs : 0 < r * s := mul_pos hr hs
    have key : r ^ (-(1 : ℝ) / 2) * s ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (r * s) := by
      rw [← Real.mul_rpow hr.le hs.le]
      rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num, Real.rpow_neg hrs.le (1 / 2),
        ← Real.sqrt_eq_rpow, inv_eq_one_div]
    calc (1 / 2) * r ^ (-(1 : ℝ) / 2) * ((1 / 2) * s ^ (-(1 : ℝ) / 2) *
            f (r ^ 2 - 2 * γ * r * s + s ^ 2))
        = (1 / 4) * ((r ^ (-(1 : ℝ) / 2) * s ^ (-(1 : ℝ) / 2)) *
            f (r ^ 2 - 2 * γ * r * s + s ^ 2)) := by ring
      _ = (1 / 4) * ((1 / Real.sqrt (r * s)) * f (r ^ 2 - 2 * γ * r * s + s ^ 2)) := by rw [key]
      _ = (1 / 4) * (f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)) := by ring
  -- Pull the constant `1/4` out of the double integral.
  have h4 : (∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          (1 / 4) * (f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)))
      = (1 / 4) * ∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s) := by
    have h4a : (∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          (1 / 4) * (f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)))
        = ∫ r in Set.Ioi 0, (1 / 4) *
            (∫ s in Set.Ioi 0, f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro r _
      simp only []
      rw [MeasureTheory.integral_const_mul]
    rw [h4a, MeasureTheory.integral_const_mul]
  calc ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
        f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      = ∫ t₁ in Set.Ioi 0, ∫ s in Set.Ioi 0,
          (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * s + s ^ 2) := h1
    _ = ∫ r in Set.Ioi 0, (1 / 2) * r ^ (-(1 : ℝ) / 2) *
          (∫ s in Set.Ioi 0,
            (1 / 2) * s ^ (-(1 : ℝ) / 2) * f (r ^ 2 - 2 * γ * r * s + s ^ 2)) := h2
    _ = ∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          (1 / 4) * (f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)) := h3
    _ = (1 / 4) * ∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
          f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s) := h4

end Work.FIArea2.SevenSix
