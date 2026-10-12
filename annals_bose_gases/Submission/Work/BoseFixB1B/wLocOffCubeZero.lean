import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.LocPotential
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open Submission.BoseGases

/-!
# `Work.BoseFixB1B.wLocOffCubeZero`

The localised one-body kernel `wLoc ℓ g u x y = χ_u(x)·W(x−y)·χ_u(y)` carries the cell bump at
*both* slots.  With the cell label `u = 0` the `y`-slot factor is `χ((ℓ⁻¹)•y) = chiScale ℓ y`,
which is supported in the centred cube `acube ℓ` (`chiScale_support_le` +
`mem_acube_of_norm_le`).  Hence `wLoc ℓ g 0 a b` vanishes as soon as `b` is outside `acube ℓ`,
regardless of the numerator `g` and the `x`-slot label `a`.

This is the pointwise support input used when localising the one-body potential at the home cell.
-/

theorem wLocOffCubeZero {ℓ : ℝ} (hℓ : 0 < ℓ) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (a : EuclideanSpace ℝ (Fin 3)) {b : EuclideanSpace ℝ (Fin 3)}
    (hb : b ∉ Submission.BoseGases.acube ℓ) :
    Submission.BoseGases.wLoc ℓ g 0 a b = 0 := by
  have hχ : Submission.BoseGases.chiU ℓ 0 b = 0 := by
    -- the `y`-slot bump is `chiScale ℓ b`, which vanishes off the centred cube
    have hz : Submission.BoseGases.chiScale ℓ b = 0 := by
      by_contra h
      exact hb (Submission.BoseGases.mem_acube_of_norm_le hℓ.le
        (Submission.BoseGases.chiScale_support_le hℓ h))
    simpa [Submission.BoseGases.chiU, Submission.BoseGases.chiScale] using hz
  simp only [Submission.BoseGases.wLoc, hχ, mul_zero]

end Work.BoseFixB1B
