import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseGateFS

/-- Relative difference of two quotients with positive denominators: the change is
controlled by the change of the numerators (divided by the *larger* denominator)
plus the change of the denominators weighted by the largest of the two ratios.
This is the sharp-constant form used for perturbing ratios `b/a` by a common scale. -/
theorem ratio_diff_bound {aP aQ bP bQ : ℝ} (hP : 0 < aP) (hQ : 0 < aQ) :
    |bP / aP - bQ / aQ| ≤ |bP - bQ| / max aP aQ
      + max (|bP| / aP) (|bQ| / aQ) * |aP - aQ| / max aP aQ := by
  set M := max (|bP| / aP) (|bQ| / aQ) with hM
  have hMgeP : |bP| / aP ≤ M := le_max_left _ _
  have hMgeQ : |bQ| / aQ ≤ M := le_max_right _ _
  rcases le_total aQ aP with h | h
  · -- `aQ ≤ aP`, so `max aP aQ = aP`
    rw [max_eq_left h]
    have h1 : |bP / aP - bQ / aQ| ≤
        |bP - bQ| / aP + |bQ| * |aP - aQ| / (aP * aQ) := by
      have key : bP / aP - bQ / aQ = (bP - bQ) / aP + bQ * (aQ - aP) / (aP * aQ) := by
        field_simp; ring
      rw [key]
      calc |(bP - bQ) / aP + bQ * (aQ - aP) / (aP * aQ)|
          ≤ |(bP - bQ) / aP| + |bQ * (aQ - aP) / (aP * aQ)| := abs_add_le _ _
        _ = |bP - bQ| / aP + |bQ| * |aP - aQ| / (aP * aQ) := by
              rw [abs_div, abs_div, abs_mul, abs_of_pos hP, abs_of_pos (mul_pos hP hQ),
                abs_sub_comm aQ aP]
    have h2 : |bQ| * |aP - aQ| / (aP * aQ) ≤ M * |aP - aQ| / aP := by
      have he : |bQ| * |aP - aQ| / (aP * aQ) = (|bQ| / aQ) * (|aP - aQ| / aP) := by
        rw [mul_comm aP aQ, ← div_mul_div_comm]
      rw [he]
      calc (|bQ| / aQ) * (|aP - aQ| / aP) ≤ M * (|aP - aQ| / aP) :=
            mul_le_mul_of_nonneg_right hMgeQ (by positivity)
        _ = M * |aP - aQ| / aP := by ring
    linarith [h1, h2]
  · -- `aP ≤ aQ`, so `max aP aQ = aQ`
    rw [max_eq_right h]
    have h1 : |bP / aP - bQ / aQ| ≤
        |bP - bQ| / aQ + |bP| * |aP - aQ| / (aP * aQ) := by
      have key : bP / aP - bQ / aQ = (bP - bQ) / aQ + bP * (aQ - aP) / (aP * aQ) := by
        field_simp; ring
      rw [key]
      calc |(bP - bQ) / aQ + bP * (aQ - aP) / (aP * aQ)|
          ≤ |(bP - bQ) / aQ| + |bP * (aQ - aP) / (aP * aQ)| := abs_add_le _ _
        _ = |bP - bQ| / aQ + |bP| * |aP - aQ| / (aP * aQ) := by
              rw [abs_div, abs_div, abs_mul, abs_of_pos hQ, abs_of_pos (mul_pos hP hQ),
                abs_sub_comm aQ aP]
    have h2 : |bP| * |aP - aQ| / (aP * aQ) ≤ M * |aP - aQ| / aQ := by
      have he : |bP| * |aP - aQ| / (aP * aQ) = (|bP| / aP) * (|aP - aQ| / aQ) := by
        rw [← div_mul_div_comm]
      rw [he]
      calc (|bP| / aP) * (|aP - aQ| / aQ) ≤ M * (|aP - aQ| / aQ) :=
            mul_le_mul_of_nonneg_right hMgeP (by positivity)
        _ = M * |aP - aQ| / aQ := by ring
    linarith [h1, h2]

end Work.BoseGateFS
