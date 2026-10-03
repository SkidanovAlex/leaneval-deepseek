/-
# `Submission.Work.FIPiChain.P2Rho.ZcExpProductLe`

The top margin of the `B`-dependent `ρ`-window of the `FI` endgame:

  `e·(sc x B · zc x B) ≤ √x·(log x)^{-B₀}`  eventually in `x`,

for every `B > 0` and every `B₀` with `B₀ + 5 ≤ B`.  This is the conjunct of `RhoWin2RangeCm`
(and the companion of `ZcLogBoundsCm`) that the `ρ`-window removal `RhoWindowInt2_ge` consumes:
the window top has to sit strictly below the top `√x(log x)^{-B₀}` of the range (4.6) of
`Prop41Statement`.

The estimate splits into two independent facts, each proved in its own module of the fleet:

* `ScZcLeSqrtLog` (`Submission/Work/FIPiChain/P2Rho/ScZcLeSqrtLog.lean`): the window top is at most
  `√x·(log x)^{-(B+2)}`.  Indeed `zc x B = ⌊Yc x B⌋₊ ≤ Yc x B` and
  `sc x B · Yc x B = √x/(log x)^{B+2}` by the definition `Yc x B = √x/(sc x B·(log x)^{B+2})`.
* `ExpMulLogRpowLe` (`Submission/Work/FIPiChain/P2Rho/ExpMulLogRpowLe.lean`): the constant
  `exp 1` is absorbed by the logarithmic gap of size `B + 2 - B₀ ≥ 7`, i.e.
  `e·(log x)^{-(B+2)} ≤ (log x)^{-B₀}` eventually.

Assembling the two only rearranges the product: `e·(sc·zc) ≤ e·(√x·L^{-(B+2)})
= √x·(e·L^{-(B+2)}) ≤ √x·L^{-B₀}`.  No `sorry`, no `axiom`.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FITop.RCPrelude
import Submission.Work.FIPiChain.P2Rho.ScZcLeSqrtLog
import Submission.Work.FIPiChain.P2Rho.ExpMulLogRpowLe

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Work.FIPiChain.P2Rho

open Filter

theorem ZcExpProductLe (B B₀ : ℝ) (hB : 0 < B) (hB₀ : B₀ + 5 ≤ B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B) ≤
        (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B₀) := by
  filter_upwards [ScZcLeSqrtLog B, ExpMulLogRpowLe B B₀ hB₀] with x htop hkey
  calc Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B)
      ≤ Real.exp 1 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(B + 2))) :=
        mul_le_mul_of_nonneg_left htop (Real.exp_pos 1).le
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.exp 1 * (Real.log (x : ℝ)) ^ (-(B + 2))) := by ring
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B₀) :=
        mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (Nat.cast_nonneg x) _)

end Work.FIPiChain.P2Rho
