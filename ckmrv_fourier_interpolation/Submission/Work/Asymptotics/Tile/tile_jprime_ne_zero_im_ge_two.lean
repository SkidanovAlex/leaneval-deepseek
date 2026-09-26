import Mathlib
import Submission.Work.Asymptotics.CuspDecay.E4Fun_second_order_im_ge_two
import Submission.Work.Asymptotics.CuspDecay.E6Fun_second_order_im_ge_two
import Submission.Work.Residues.ResidueKernel
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc

namespace Work.Asymptotics.Tile

/-- **`j'` does not vanish above height `2`.**  Since `j' = -2πi E₄²E₆/Δ` and both `E₄` and
`E₆` are within `O(‖q‖)` of `1` on `Im ≥ 2` (with `‖q‖ = e^{-2π Im} ≤ e^{-4π} ≤ 1/40000`), while
`Δ ≠ 0`, we have `jprime ρ ≠ 0` for `2 ≤ ρ.im`. -/
theorem tile_jprime_ne_zero_im_ge_two (ρ : UpperHalfPlane) (h : 2 ≤ ρ.im) :
    Work.Residues.jprime ρ ≠ 0 := by
  -- `j' = -2πi E₄²E₆/Δ` vanishes exactly where `E₄` or `E₆` does (`Δ` never vanishes).
  rw [Work.Residues.jprime_ne_zero_iff]
  refine mul_ne_zero ?_ ?_
  · -- `‖E₄ ρ - 1‖ ≤ 1/2`, so `E₄ ρ ≠ 0`.
    intro h0
    have hle := Work.FunnelNumerics.E4_sub_one_le ρ h
    rw [h0, zero_sub, norm_neg, norm_one] at hle
    norm_num at hle
  · -- `E₆ ρ ≠ 0` at height `≥ 2`.
    exact Work.Asymptotics.SpikeCircle.E6Fun_ne_zero_im ρ h

end Work.Asymptotics.Tile
