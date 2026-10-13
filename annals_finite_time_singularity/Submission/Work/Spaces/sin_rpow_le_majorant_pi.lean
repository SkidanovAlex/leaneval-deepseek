import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Spaces

/-- Core Jordan-type estimate: for `0 < p` and `x ∈ [0, π/4]`,
`(sin (2 x)) ^ (-p) ≤ (π/4) ^ p * x ^ (-p)`.

Jordan's inequality `(2/π) y ≤ sin y` on `[0, π/2]`, applied to `y = 2 x`, gives
`sin (2 x) ≥ (4/π) x`; raising to the non-positive power `-p` reverses the
inequality and the constant `(4/π) ^ (-p)` is rewritten as `(π/4) ^ p`. -/
private lemma sin_two_mul_rpow_le_of_le_pi_div_four (p x : ℝ) (hp : 0 < p)
    (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * x)) ^ (-p) ≤ (Real.pi / 4) ^ p * x ^ (-p) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [mul_zero, Real.sin_zero, Real.zero_rpow (by linarith : (-p) ≠ 0), mul_zero]
  · have h2x0 : 0 ≤ 2 * x := by linarith
    have h2x1 : 2 * x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have hj := Real.mul_le_sin h2x0 h2x1
    have hjeq : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
    rw [hjeq] at hj
    have hpos : 0 < (4 / Real.pi) * x := by positivity
    have key := Real.rpow_le_rpow_of_nonpos hpos hj (show -p ≤ 0 by linarith)
    have hcoef : (4 / Real.pi : ℝ) ^ (-p) = (Real.pi / 4) ^ p := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
          ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) p, inv_div]
    have hmr : ((4 / Real.pi) * x) ^ (-p) = (Real.pi / 4) ^ p * x ^ (-p) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (le_of_lt h), hcoef]
    rw [hmr] at key
    exact key

/-- For `0 < p` and `θ ∈ [0, π/2]`,
`(sin (2 θ)) ^ (-p) ≤ (π/4) ^ p * (θ ^ (-p) + (π/2 - θ) ^ (-p))`.

The estimate is invariant under the reflection `θ ↦ π/2 - θ` (because
`sin (π - 2θ) = sin (2θ)`), so it suffices to treat `θ ≤ π/4`.  There Jordan's
inequality `sin (2θ) ≥ (4/π) θ` gives `(sin (2θ)) ^ (-p) ≤ (π/4) ^ p * θ ^ (-p)`,
and the positive term `(π/2 - θ) ^ (-p)` may be added freely. -/
theorem sin_rpow_le_majorant_pi (p θ : ℝ) (hp : 0 < p) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-p) ≤ (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases le_total θ (Real.pi / 4) with h | h
  · have hcore := sin_two_mul_rpow_le_of_le_pi_div_four p θ hp ⟨hθ0, h⟩
    have h1 : θ ^ (-p) ≤ θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p) :=
      le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - θ) (-p))
    have hle : (Real.pi / 4) ^ p * θ ^ (-p) ≤
        (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p)
    linarith
  · have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      have h2 : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
      rw [h2, Real.sin_pi_sub]
    have hcore := sin_two_mul_rpow_le_of_le_pi_div_four p (Real.pi / 2 - θ) hp
      ⟨by linarith, by linarith⟩
    rw [hsin]
    have h1 : (Real.pi / 2 - θ) ^ (-p) ≤ θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p) :=
      le_add_of_nonneg_left (Real.rpow_nonneg hθ0 (-p))
    have hle : (Real.pi / 4) ^ p * (Real.pi / 2 - θ) ^ (-p) ≤
        (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p)
    linarith

end Work.Spaces
