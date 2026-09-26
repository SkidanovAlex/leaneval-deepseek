/-
# The tile divisor lower bound at the *sharp* threshold `Im (S • w) + 1`

The proved `Tile.ktl8_tile_divisor_lower` (in `Tile/KPlus8TileTail.lean`) bounds the divisor
`Δ(z) (j(n +ᵥ w) − j z)` below by `1/16` on the cusp-`±1` tiles, but only under the *crude*
threshold `2 Im(S • w) + 1 ≤ t` of the `TB`-calculus.  Its proof, however, only uses
`funnel_divisor_lower` at the funnel point `S • w`, whose hypothesis is the *sharp* threshold
`Im (S • w) + 1 ≤ t`.  This file records the sharp-threshold version, which is what a
sharp-threshold tile tail needs.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.KMinusTileTail
import Submission.Work.Asymptotics.funnel_divisor_lower

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **The divisor lower bound on the tiles at the sharp threshold.**
For `w ∈ E`, `n = ±1`, `z = i t` with `t ≥ Im (S • w) + 1`,
`1/16 ≤ ‖Δ z · (j (n +ᵥ w) − j z)‖`. -/
lemma tileDivisorLowerSharp (w : UpperHalfPlane) (hw : w ∈ Work.Asymptotics.KEpsilon)
    (z : UpperHalfPlane) (t : ℝ) (hz : (z : ℂ) = (t : ℂ) * Complex.I)
    (ht : (ModularGroup.S • w).im + 1 ≤ t) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    (1 / 16 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖ := by
  have hτF : Work.Asymptotics.Funnel (ModularGroup.S • w) :=
    ⟨Work.Asymptotics.S_smul_mem_DomainD hw.1, hw.2⟩
  have h := Work.Asymptotics.funnel_divisor_lower (ModularGroup.S • w) z t hτF ht hz
  have hj : Work.Kernels.jInvariantFun (ModularGroup.S • w)
      = Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) := by
    rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul, ktl_jInvariantFun_vadd_int n hn w]
  rwa [hj] at h

/-- The reciprocal divisor is uniformly bounded on the tiles at the sharp threshold. -/
lemma tile_invDivisor_le_sharp (w : UpperHalfPlane) (hw : w ∈ Work.Asymptotics.KEpsilon)
    (z : UpperHalfPlane) (t : ℝ) (hz : (z : ℂ) = (t : ℂ) * Complex.I)
    (ht : (ModularGroup.S • w).im + 1 ≤ t) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ‖(Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z))⁻¹‖
      ≤ 16 := by
  have h := tileDivisorLowerSharp w hw z t hz ht n hn
  have hpos : 0 < ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖ :=
    lt_of_lt_of_le (by norm_num) h
  rw [norm_inv]
  rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 16)]
  rw [show ((16 : ℝ))⁻¹ = 1 / 16 by norm_num]
  exact h

end

end Work.Asymptotics.Tile
