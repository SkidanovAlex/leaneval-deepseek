import Mathlib
import Submission.Work.EQ.hetero_leaf

namespace Work.EQ

/-- Joint Lipschitz estimate for the `x`-displacement `locA` of the two-step map, obtained by
splitting the difference through the intermediate point `(x₁, y₂)` and applying the `x`-Lipschitz
field (`lipX`) at height `y₂` and the `y`-Lipschitz field (`lipY`) at abscissa `x₁`. -/
theorem locA_pair_lip {a : ℝ} (d : Work.EQ.LocData a) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : |x₁| ≤ 3 * d.ρ) (hx₂ : |x₂| ≤ 3 * d.ρ)
    (hy₁0 : 0 < y₁) (hy₁h : y₁ ≤ d.h) (hy₂0 : 0 < y₂) (hy₂h : y₂ ≤ d.h) :
    |Work.EQ.locA a (x₂, y₂) - Work.EQ.locA a (x₁, y₁)| ≤
      d.C * y₂ ^ 2 * |x₂ - x₁| + d.C * (y₁ + y₂) * |y₂ - y₁| := by
  have hX := (d.lipX x₁ x₂ y₂ hx₁ hx₂ hy₂0 hy₂h).1
  have hY := (d.lipY x₁ y₁ y₂ hx₁ hy₁0 hy₁h hy₂0 hy₂h).1
  have h1 : |locA a (x₂, y₂) - locA a (x₁, y₂)| ≤ d.C * y₂ ^ 2 * |x₂ - x₁| := by
    rw [abs_sub_comm x₁ x₂, abs_sub_comm (locA a (x₁, y₂)) (locA a (x₂, y₂))] at hX
    exact hX
  have h2 : |locA a (x₁, y₂) - locA a (x₁, y₁)| ≤ d.C * (y₁ + y₂) * |y₂ - y₁| := by
    rw [abs_sub_comm y₁ y₂, abs_sub_comm (locA a (x₁, y₁)) (locA a (x₁, y₂))] at hY
    exact hY
  have hsplit : locA a (x₂, y₂) - locA a (x₁, y₁) =
      (locA a (x₂, y₂) - locA a (x₁, y₂)) + (locA a (x₁, y₂) - locA a (x₁, y₁)) := by ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

end Work.EQ
