import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- **Elementwise bound for `v θ + sin θ cos θ · v' θ` near `θ = π/2`.**

Given the two endpoint Taylor estimates at `θ = π/2` for a `C²` function `v` with slope
`a` at `π/2` and second-derivative bound `B ≥ 0`, namely
`|v θ + a * (π/2 - θ)| ≤ B / 2 * (π/2 - θ) ^ 2` and `|dv θ - a| ≤ B * (π/2 - θ)`
(here `dv` is the derivative of `v`), the (singular) combination
`v θ + sin θ cos θ · dv θ` is `O(cos²θ)`:

`|v θ + Real.sin θ * Real.cos θ * dv θ| ≤ (B * π ^ 2 / 8 + |a| * π ^ 3 / 12 + B * (π / 2)) * cos θ ^ 2`.

Route: with `δ = π/2 - θ`, `sin θ cos θ = sin (2δ) / 2`, so writing `v = E - a δ` and
`dv = a + F` with `|E| ≤ (B/2)δ²`, `|F| ≤ B δ` one has
`v θ + sin θ cos θ dv θ = E + a (sin (2δ)/2 - δ) + sin θ cos θ F`; bound the three pieces by
`(B/2)δ²`, `|a| (2/3) δ³` (`Real.abs_sub_sin_le` at `2δ`) and `B δ cos θ`, then use
`δ ≤ (π/2) cos θ` (`Real.mul_le_sin`, since `cos θ = sin δ`). -/
theorem GWeightBound {v dv : ℝ → ℝ} {a B θ : ℝ} (hB : 0 ≤ B)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (h2 : |v θ + a * (Real.pi / 2 - θ)| ≤ B / 2 * (Real.pi / 2 - θ) ^ 2)
    (h1 : |dv θ - a| ≤ B * (Real.pi / 2 - θ)) :
    |v θ + Real.sin θ * Real.cos θ * dv θ| ≤
      (B * Real.pi ^ 2 / 8 + |a| * Real.pi ^ 3 / 12 + B * (Real.pi / 2)) * Real.cos θ ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- shift the origin to `θ = π / 2`
  set δ : ℝ := Real.pi / 2 - θ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδlt : δ < Real.pi / 2 := by rw [hδdef]; linarith
  have hθeq : θ = Real.pi / 2 - δ := by rw [hδdef]; ring
  have hcos : Real.cos θ = Real.sin δ := by rw [hθeq, Real.cos_pi_div_two_sub]
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hcosθ : 0 < Real.cos θ := by
    rw [hcos]; exact Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith)
  have h2' : |v θ + a * δ| ≤ B / 2 * δ ^ 2 := by rw [hδdef]; exact h2
  have h1' : |dv θ - a| ≤ B * δ := by rw [hδdef]; exact h1
  -- `sin θ cos θ = sin (2δ) / 2`
  have h2θ : 2 * θ = Real.pi - 2 * δ := by rw [hδdef]; ring
  have hs2 : Real.sin (2 * θ) = Real.sin (2 * δ) := by rw [h2θ, Real.sin_pi_sub]
  have hsc : Real.sin θ * Real.cos θ = Real.sin (2 * δ) / 2 := by
    rw [← hs2, Real.sin_two_mul]; ring
  have hSCnn : 0 ≤ Real.sin θ * Real.cos θ := (mul_pos hsinθ hcosθ).le
  -- `δ ≤ (π / 2) * cos θ`
  have hδle : δ ≤ Real.pi / 2 * Real.cos θ := by
    rw [hcos]
    have hs := Real.mul_le_sin hδpos.le hδlt.le
    have hmul := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    have he : Real.pi / 2 * (2 / Real.pi * δ) = δ := by field_simp
    linarith
  -- the three pieces
  have hb1 : |v θ + a * δ| ≤ B * Real.pi ^ 2 / 8 * Real.cos θ ^ 2 := by
    have hc : 0 ≤ Real.pi / 2 * Real.cos θ := by positivity
    have hsq : δ ^ 2 ≤ (Real.pi / 2 * Real.cos θ) ^ 2 := pow_le_pow_left₀ hδpos.le hδle 2
    calc |v θ + a * δ| ≤ B / 2 * δ ^ 2 := h2'
      _ ≤ B / 2 * (Real.pi / 2 * Real.cos θ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = B * Real.pi ^ 2 / 8 * Real.cos θ ^ 2 := by ring
  have hbd : |Real.sin (2 * δ) / 2 - δ| ≤ 2 / 3 * δ ^ 3 := by
    have h := Real.abs_sub_sin_le (2 * δ)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * δ)] at h
    have h2b : |Real.sin (2 * δ) / 2 - δ| = |2 * δ - Real.sin (2 * δ)| / 2 := by
      rw [show Real.sin (2 * δ) / 2 - δ = -(2 * δ - Real.sin (2 * δ)) / 2 by ring]
      rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h2b]
    calc |2 * δ - Real.sin (2 * δ)| / 2 ≤ ((2 * δ) ^ 3 / 6) / 2 :=
          div_le_div_of_nonneg_right h (by norm_num)
      _ = 2 / 3 * δ ^ 3 := by ring
  have hb2 : |a| * |Real.sin θ * Real.cos θ - δ| ≤ |a| * Real.pi ^ 3 / 12 * Real.cos θ ^ 2 := by
    rw [hsc]
    have hcube1 : δ ^ 3 ≤ (Real.pi / 2 * Real.cos θ) ^ 3 := pow_le_pow_left₀ hδpos.le hδle 3
    have hbd2 : |Real.sin (2 * δ) / 2 - δ| ≤ Real.pi ^ 3 / 12 * Real.cos θ ^ 2 := by
      have hc3 : Real.cos θ ^ 3 ≤ Real.cos θ ^ 2 := by
        have h1c := Real.cos_le_one θ
        nlinarith [hcosθ]
      calc |Real.sin (2 * δ) / 2 - δ| ≤ 2 / 3 * δ ^ 3 := hbd
        _ ≤ 2 / 3 * (Real.pi / 2 * Real.cos θ) ^ 3 := mul_le_mul_of_nonneg_left hcube1 (by norm_num)
        _ = Real.pi ^ 3 / 12 * Real.cos θ ^ 3 := by ring
        _ ≤ Real.pi ^ 3 / 12 * Real.cos θ ^ 2 := mul_le_mul_of_nonneg_left hc3 (by positivity)
    calc |a| * |Real.sin (2 * δ) / 2 - δ| ≤ |a| * (Real.pi ^ 3 / 12 * Real.cos θ ^ 2) :=
          mul_le_mul_of_nonneg_left hbd2 (abs_nonneg a)
      _ = |a| * Real.pi ^ 3 / 12 * Real.cos θ ^ 2 := by ring
  have hb3 : Real.sin θ * Real.cos θ * |dv θ - a| ≤ B * (Real.pi / 2) * Real.cos θ ^ 2 := by
    have hBδ : 0 ≤ B * δ := mul_nonneg hB hδpos.le
    have hsc_le : Real.sin θ * Real.cos θ ≤ Real.cos θ := by
      simpa using mul_le_mul_of_nonneg_right (Real.sin_le_one θ) hcosθ.le
    calc Real.sin θ * Real.cos θ * |dv θ - a| ≤ Real.sin θ * Real.cos θ * (B * δ) :=
          mul_le_mul_of_nonneg_left h1' hSCnn
      _ = B * δ * (Real.sin θ * Real.cos θ) := by ring
      _ ≤ B * δ * Real.cos θ := mul_le_mul_of_nonneg_left hsc_le hBδ
      _ ≤ B * (Real.pi / 2 * Real.cos θ) * Real.cos θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδle hB) hcosθ.le
      _ = B * (Real.pi / 2) * Real.cos θ ^ 2 := by ring
  -- decompose and assemble
  have hmain : |v θ + Real.sin θ * Real.cos θ * dv θ|
      ≤ |v θ + a * δ| + |a| * |Real.sin θ * Real.cos θ - δ|
        + Real.sin θ * Real.cos θ * |dv θ - a| := by
    have hdec : v θ + Real.sin θ * Real.cos θ * dv θ
        = (v θ + a * δ) + a * (Real.sin θ * Real.cos θ - δ)
          + Real.sin θ * Real.cos θ * (dv θ - a) := by ring
    rw [hdec]
    have h1t : |(v θ + a * δ) + a * (Real.sin θ * Real.cos θ - δ)
          + Real.sin θ * Real.cos θ * (dv θ - a)|
        ≤ |(v θ + a * δ) + a * (Real.sin θ * Real.cos θ - δ)|
          + |Real.sin θ * Real.cos θ * (dv θ - a)| :=
      abs_add_le _ _
    have h2t : |(v θ + a * δ) + a * (Real.sin θ * Real.cos θ - δ)|
        ≤ |v θ + a * δ| + |a * (Real.sin θ * Real.cos θ - δ)| := abs_add_le _ _
    have h3t : |Real.sin θ * Real.cos θ * (dv θ - a)|
        = Real.sin θ * Real.cos θ * |dv θ - a| := by
      rw [abs_mul, abs_of_nonneg hSCnn]
    have h4t : |a * (Real.sin θ * Real.cos θ - δ)| = |a| * |Real.sin θ * Real.cos θ - δ| := by
      rw [abs_mul]
    linarith [h1t, h2t, h3t, h4t]
  calc |v θ + Real.sin θ * Real.cos θ * dv θ|
      ≤ |v θ + a * δ| + |a| * |Real.sin θ * Real.cos θ - δ|
        + Real.sin θ * Real.cos θ * |dv θ - a| := hmain
    _ ≤ B * Real.pi ^ 2 / 8 * Real.cos θ ^ 2 + |a| * Real.pi ^ 3 / 12 * Real.cos θ ^ 2
        + B * (Real.pi / 2) * Real.cos θ ^ 2 := by linarith [hb1, hb2, hb3]
    _ = (B * Real.pi ^ 2 / 8 + |a| * Real.pi ^ 3 / 12 + B * (Real.pi / 2)) * Real.cos θ ^ 2 := by
        ring

end Work.FTS.PhiStar.Honesty
