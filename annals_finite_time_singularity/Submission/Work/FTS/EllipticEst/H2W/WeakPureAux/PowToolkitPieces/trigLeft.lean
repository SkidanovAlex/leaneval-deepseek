import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces

/-- The elementary trigonometric comparison behind the `s ∈ (0, π/4]` half of the power
toolkit.  On this range `2s ∈ (0, π/2]`, so **Jordan's inequality** `2x/π ≤ sin x` gives
`sin(2s) ≥ 4s/π`, while `cos` is decreasing on `[0, π/3]` with `cos(π/3) = 1/2`, so
`cos s ≥ 1/2`.  Hence `cos s · sin(2s)² ≥ (1/2)(4s/π)² = 8s²/π²`, i.e.
`1/(cos s · sin(2s)²) ≤ π²/(8s²)`. -/
theorem trigLeft :
    ∀ s ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) ≤ (Real.pi ^ 2 / 8) / s ^ 2 := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  -- Jordan's inequality on `2s ∈ (0, π/2]`
  have hsin : 2 / Real.pi * (2 * s) ≤ Real.sin (2 * s) :=
    Real.mul_le_sin (by linarith) (by linarith [hs2])
  have hsin2 : (2 / Real.pi * (2 * s)) ^ 2 ≤ (Real.sin (2 * s)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  -- `cos s ≥ cos (π/3) = 1/2`, since `s ≤ π/4 ≤ π/3` and `cos` is decreasing on `[0, π]`
  have hcos : 1 / 2 ≤ Real.cos s := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := s) (y := Real.pi / 3)
      hs1.le (by linarith [Real.pi_pos]) (by linarith [hs2, Real.pi_pos])
    rwa [Real.cos_pi_div_three] at h
  -- combine the two lower bounds
  have hmain : 8 * s ^ 2 / Real.pi ^ 2 ≤ Real.cos s * (Real.sin (2 * s)) ^ 2 := by
    have harith : (1 / 2 : ℝ) * (2 / Real.pi * (2 * s)) ^ 2 = 8 * s ^ 2 / Real.pi ^ 2 := by
      field_simp
      ring
    rw [← harith]
    exact mul_le_mul_of_nonneg hcos hsin2 (by norm_num) (sq_nonneg _)
  have hmain' : s ^ 2 ≤ (Real.pi ^ 2 / 8) * (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
    have h1 : (Real.pi ^ 2 / 8) * (8 * s ^ 2 / Real.pi ^ 2) = s ^ 2 := by field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hmain (by positivity)
  -- convert `s² ≤ C · cos s · sin(2s)²` into the displayed division inequality
  have hden : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
    lt_of_lt_of_le (by positivity) hmain
  have hs2pos : 0 < s ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hs2pos]
  simpa using hmain'

end Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces
