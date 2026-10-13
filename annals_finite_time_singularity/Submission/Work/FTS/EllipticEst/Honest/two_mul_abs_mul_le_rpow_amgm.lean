import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.EllipticEst.Honest

/-- Young's / AM–GM inequality `2 a b ≤ a² + b²` for real `a`, `b`
(specialisation of `two_mul_le_add_sq`). -/
private lemma two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
  two_mul_le_add_sq a b

theorem two_mul_abs_mul_le_rpow_amgm {η P g u w s : ℝ} (hη : 0 < η) (hu : 0 < u) (hw : 0 < w)
    (hs : 0 ≤ s) (hcase : 0 < s ∨ g = 0) :
    2 * |P| * g ≤ (1 / u ^ 2) * ((u ^ 2 * P) ^ 2 * w ^ 2 * s ^ (-η))
      + (1 / (u ^ 2 * w ^ 2)) * g ^ 2 * s ^ η := by
  -- the right-hand side is always nonnegative
  have hRnonneg : 0 ≤ (1 / u ^ 2) * ((u ^ 2 * P) ^ 2 * w ^ 2 * s ^ (-η))
      + (1 / (u ^ 2 * w ^ 2)) * g ^ 2 * s ^ η := by
    have h1 : (0 : ℝ) ≤ (1 / u ^ 2) * ((u ^ 2 * P) ^ 2 * w ^ 2 * s ^ (-η)) :=
      mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _))
    have h2 : (0 : ℝ) ≤ (1 / (u ^ 2 * w ^ 2)) * g ^ 2 * s ^ η :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (Real.rpow_nonneg hs _)
    linarith
  rcases lt_trichotomy g 0 with hg | hg | hg
  · -- `g < 0`: the left-hand side is `≤ 0`
    have h2 : 0 ≤ 2 * |P| := by positivity
    have : 2 * |P| * g ≤ 0 := by nlinarith
    linarith
  · -- `g = 0`
    subst hg
    simpa using hRnonneg
  · -- `g > 0`: write the two right-hand terms as squares and apply AM–GM
    have hs' : 0 < s := hcase.resolve_right (ne_of_gt hg)
    have hsp1 : s ^ (-η / 2) * s ^ (η / 2) = 1 := by
      rw [← Real.rpow_add hs', show -η / 2 + η / 2 = 0 by ring, Real.rpow_zero]
    have hX2 : (u * |P| * w * s ^ (-η / 2)) ^ 2
        = (1 / u ^ 2) * ((u ^ 2 * P) ^ 2 * w ^ 2 * s ^ (-η)) := by
      have hsp2 : (s ^ (-η / 2)) ^ 2 = s ^ (-η) := by
        rw [sq, ← Real.rpow_add hs']; congr 1; ring
      rw [show (u * |P| * w * s ^ (-η / 2)) ^ 2
          = u ^ 2 * |P| ^ 2 * w ^ 2 * (s ^ (-η / 2)) ^ 2 by ring]
      rw [hsp2, sq_abs]
      field_simp
    have hY2 : (g * s ^ (η / 2) / (u * w)) ^ 2
        = (1 / (u ^ 2 * w ^ 2)) * g ^ 2 * s ^ η := by
      have hsp2 : (s ^ (η / 2)) ^ 2 = s ^ η := by
        rw [sq, ← Real.rpow_add hs']; congr 1; ring
      rw [div_pow, mul_pow, hsp2]
      field_simp
    have hXY : (u * |P| * w * s ^ (-η / 2)) * (g * s ^ (η / 2) / (u * w)) = |P| * g := by
      rw [show u * |P| * w * s ^ (-η / 2) * (g * s ^ (η / 2) / (u * w))
          = (u * |P| * w) * (g / (u * w)) * (s ^ (-η / 2) * s ^ (η / 2)) by ring]
      rw [hsp1, mul_one]
      field_simp
    have hkey : 2 * ((u * |P| * w * s ^ (-η / 2)) * (g * s ^ (η / 2) / (u * w)))
        ≤ (u * |P| * w * s ^ (-η / 2)) ^ 2 + (g * s ^ (η / 2) / (u * w)) ^ 2 := by
      nlinarith [sq_nonneg ((u * |P| * w * s ^ (-η / 2)) - (g * s ^ (η / 2) / (u * w)))]
    rw [hXY, hX2, hY2] at hkey
    rw [show (2 : ℝ) * (|P| * g) = 2 * |P| * g by ring] at hkey
    exact hkey

end Work.FTS.EllipticEst.Honest
