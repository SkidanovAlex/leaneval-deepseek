import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4


open scoped Real BigOperators Topology

/-- Faithful quartic error comparison.  Suggested route: normalise the LHS to
`(65536/3) * Real.pi^2 * (M*(M+1)^3 / s^9) * (av^4 / c0^3)` (`field_simp; ring`) and the RHS
to `C * (M^4 / s^9) * (av^4 / c0^3)`; cancel the positive factors and use
`((M+1)/M)^3 ≤ 27/8` from `2 ≤ M`, together with
`(65536/3)*π^2*(27/8) = 73728*π^2 ≤ 27 * ((16*π)^4/(3*π^2)) = 589824*π^2 ≤ C`. -/
lemma d1_quart_arith_F {M s c0 av C : ℝ} (hs : 0 < s) (hM2 : 2 ≤ M) (hc0 : 0 < c0)
    (hav : 0 < av) (hC : 27 * ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) ≤ C) :
    M * ((2 * Real.pi) ^ 3)⁻¹
        * (((M + 1) ^ 3 / (4 * s ^ 9))
            * (64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)))
      ≤ C * (av ^ 4 * (c0 ^ 3)⁻¹ * (((M / s ^ 3) ^ 3) * ((M / s ^ 3)) * s ^ 3)) := by
  have hLHS : M * ((2 * Real.pi) ^ 3)⁻¹
        * (((M + 1) ^ 3 / (4 * s ^ 9))
            * (64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)))
      = (65536 / 3) * Real.pi ^ 2 * (M * (M + 1) ^ 3 / s ^ 9) * (av ^ 4 / c0 ^ 3) := by
    field_simp
    ring
  have hRHS : C * (av ^ 4 * (c0 ^ 3)⁻¹ * (((M / s ^ 3) ^ 3) * ((M / s ^ 3)) * s ^ 3))
      = C * (M ^ 4 / s ^ 9) * (av ^ 4 / c0 ^ 3) := by
    field_simp
  rw [hLHS, hRHS]
  have hMpos : 0 < M := by linarith
  have hsp9 : (0:ℝ) < s ^ 9 := by positivity
  have hcube : (M + 1) ^ 3 ≤ (27 / 8) * M ^ 3 := by
    have h1 : M + 1 ≤ (3 / 2) * M := by linarith
    have h3 : (M + 1) ^ 3 ≤ ((3 / 2) * M) ^ 3 := by
      apply pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ M + 1) h1
    calc (M + 1) ^ 3 ≤ ((3 / 2) * M) ^ 3 := h3
      _ = (27 / 8) * M ^ 3 := by ring
  have hC' : 73728 * Real.pi ^ 2 ≤ C := by
    have hid : 27 * ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) = 589824 * Real.pi ^ 2 := by
      field_simp
      ring
    rw [hid] at hC
    nlinarith [hC, sq_nonneg Real.pi]
  have hnum : (65536 / 3) * Real.pi ^ 2 * (M * (M + 1) ^ 3) ≤ C * M ^ 4 := by
    calc (65536 / 3) * Real.pi ^ 2 * (M * (M + 1) ^ 3)
        = (65536 / 3) * Real.pi ^ 2 * M * (M + 1) ^ 3 := by ring
      _ ≤ (65536 / 3) * Real.pi ^ 2 * M * ((27 / 8) * M ^ 3) := by
            apply mul_le_mul_of_nonneg_left hcube
            positivity
      _ = ((65536 / 3) * Real.pi ^ 2 * (27 / 8)) * M ^ 4 := by ring
      _ = 73728 * Real.pi ^ 2 * M ^ 4 := by ring
      _ ≤ C * M ^ 4 := mul_le_mul_of_nonneg_right hC' (by positivity)
  have hy : (0:ℝ) ≤ av ^ 4 / c0 ^ 3 := by positivity
  have hdiv : (65536 / 3) * Real.pi ^ 2 * (M * (M + 1) ^ 3) / s ^ 9 ≤ C * M ^ 4 / s ^ 9 :=
    div_le_div_of_nonneg_right hnum (le_of_lt hsp9)
  have hstep := mul_le_mul_of_nonneg_right hdiv hy
  calc (65536 / 3) * Real.pi ^ 2 * (M * (M + 1) ^ 3 / s ^ 9) * (av ^ 4 / c0 ^ 3)
      = (65536 / 3) * Real.pi ^ 2 * (M * (M + 1) ^ 3) / s ^ 9 * (av ^ 4 / c0 ^ 3) := by ring
    _ ≤ C * M ^ 4 / s ^ 9 * (av ^ 4 / c0 ^ 3) := hstep
    _ = C * (M ^ 4 / s ^ 9) * (av ^ 4 / c0 ^ 3) := by ring

end Work.BlockBound4
