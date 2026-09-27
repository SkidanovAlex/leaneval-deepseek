import Mathlib
import Submission.Work.EQ.hetero_leaf

namespace Work.EQ

/-- Joint Lipschitz estimate for the two-step `y`-multiplier `locM` on the box
`|x| ≤ 3ρ`, `0 < y ≤ h`: insert the intermediate point `(x₂, y₁)` and apply the two
one-variable Lipschitz bounds `LocData.lipY` (in `y`) and `LocData.lipX` (in `x`). -/
theorem locM_pair_lip {a : ℝ} (d : Work.EQ.LocData a) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : |x₁| ≤ 3 * d.ρ) (hx₂ : |x₂| ≤ 3 * d.ρ)
    (hy₁0 : 0 < y₁) (hy₁h : y₁ ≤ d.h) (hy₂0 : 0 < y₂) (hy₂h : y₂ ≤ d.h) :
    |Work.EQ.locM a (x₂, y₂) - Work.EQ.locM a (x₁, y₁)| ≤
      d.C * |x₂ - x₁| + d.C * |y₂ - y₁| := by
  have hY : |locM a (x₂, y₂) - locM a (x₂, y₁)| ≤ d.C * |y₂ - y₁| :=
    (d.lipY x₂ y₂ y₁ hx₂ hy₂0 hy₂h hy₁0 hy₁h).2
  have hX : |locM a (x₂, y₁) - locM a (x₁, y₁)| ≤ d.C * |x₂ - x₁| :=
    (d.lipX x₂ x₁ y₁ hx₂ hx₁ hy₁0 hy₁h).2
  calc |locM a (x₂, y₂) - locM a (x₁, y₁)|
      = |(locM a (x₂, y₂) - locM a (x₂, y₁)) + (locM a (x₂, y₁) - locM a (x₁, y₁))| := by
        ring_nf
    _ ≤ |locM a (x₂, y₂) - locM a (x₂, y₁)| + |locM a (x₂, y₁) - locM a (x₁, y₁)| :=
        abs_add_le _ _
    _ ≤ d.C * |y₂ - y₁| + d.C * |x₂ - x₁| := add_le_add hY hX
    _ = d.C * |x₂ - x₁| + d.C * |y₂ - y₁| := by ring

end Work.EQ
