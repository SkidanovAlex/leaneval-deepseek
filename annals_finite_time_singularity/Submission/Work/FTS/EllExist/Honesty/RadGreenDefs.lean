/-
# `Work.FTS.EllExist.Honesty.RadGreenDefs` — the two Green terms of `radGreen`

`Work.FTS.PhiStar.Radial.radGreen α m c` is the decaying solution of the mode-`m` radial Euler
equation `-α²z²a'' - α(5+α)z a' + λ_m a = c` (`λ_m = 2m(2m+5)`), written as the explicit Euler
Green function

  `radGreen α m c z = 1/(α(4m+5))·( z^{s⁻}∫_0^z c t t^{-1-s⁻}dt  +  z^{s⁺}∫_z^∞ c t t^{-1-s⁺}dt )`

with `s⁻ = -(2m+5)/α` and `s⁺ = 2m/α`.  This file names the two summands `G1` (`z^{s⁻}`-term,
singular at `z = 0`) and `G2` (`z^{s⁺}`-term, controlled by the decay hypothesis at `∞`), records
the definitional identity `radGreen = K·(G1 + G2)`, and collects the elementary exponent facts
used to bound the two terms near `z = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- The first (`z^{s⁻}`, `s⁻ = -(2m+5)/α`) Green term of `radGreen`: the integral of `c` from `0`
to `z`.  It is the term that is singular at `z = 0`. -/
def G1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))

/-- The second (`z^{s⁺}`, `s⁺ = 2m/α`) Green term of `radGreen`: the tail integral of `c`
from `z` to `∞`.  It vanishes at `z = 0` like `z^{s⁺}` provided the tail integral is finite. -/
def G2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))

/-- The explicit definition of `radGreen`, split into its two Green terms. -/
theorem radGreen_eq_G1_add_G2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = 1 / (α * (4 * (m : ℝ) + 5)) * (G1 α m c z + G2 α m c z) := rfl

/-- `s⁺ = 2m/α ≥ 8` on the standing range `0 < α ≤ 1/4`, `1 ≤ m`. -/
theorem eight_le_two_m_div (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) :
    8 ≤ 2 * (m : ℝ) / α := by
  have h4 : 4 ≤ 1 / α := by
    rw [le_div_iff₀ hα]
    linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have : 2 * (m : ℝ) / α = 2 * (m : ℝ) * (1 / α) := by ring
  rw [this]
  nlinarith

/-- `2·s⁺ - 4 = 4m/α - 4 > -1` on the standing range. -/
theorem gt_neg_one_two_m_div (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) :
    -1 < 4 * (m : ℝ) / α - 4 := by
  have h8 := eight_le_two_m_div α hα hα4 m hm
  have : 4 * (m : ℝ) / α = 2 * (2 * (m : ℝ) / α) := by ring
  rw [this]
  linarith

end Work.FTS.EllExist.Honesty
