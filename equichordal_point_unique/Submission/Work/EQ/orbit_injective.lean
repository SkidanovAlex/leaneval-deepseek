import Mathlib

namespace Work.EQ

/-- For a real base `L` with `0 < L < 1`, the integer powers of `L`, embedded in `ℂ`
and scaled by a fixed nonzero complex number `z`, are pairwise distinct in the
exponent.  Equivalently, the orbit `n ↦ L^n · z` of `z` under the dilation group is
injective. -/
theorem orbit_injective {L : ℝ} (hL0 : 0 < L) (hL1 : L < 1) {z : ℂ} (hz : z ≠ 0) :
    Function.Injective (fun n : ℤ => ((L ^ n : ℝ) : ℂ) * z) := by
  intro m n h
  -- Cancel the common nonzero factor `z`.
  have hmul : ((L ^ m : ℝ) : ℂ) = ((L ^ n : ℝ) : ℂ) := mul_right_cancel₀ hz h
  -- Descend to `ℝ` via injectivity of the real embedding.
  have hreal : L ^ m = L ^ n := Complex.ofReal_inj.mp hmul
  -- `zpow` with base in `(0,1)` is strictly antitone, hence injective in the exponent.
  exact zpow_right_injective₀ hL0 (ne_of_lt hL1) hreal

end Work.EQ
