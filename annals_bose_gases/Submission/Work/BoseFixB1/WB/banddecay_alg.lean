import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.banddecay_alg` — the exponent arithmetic of the bad-band decay

The bad-band (`I₋ᶜ`) mass of the sliding localisation carries the factor

  `12 · (1 + d)² · chiSmallBandDecay 48 d · 2^96 · (μa³)^16`

with `d = (μa³)^{6/323}`.  Since
`chiSmallBandDecay 48 d = chiSupAbs² · (chiSmallDecay 48)² · d^{-96}`, we have

  `d^{-96} = (μa³)^{-96·(6/323)} = (μa³)^{-576/323}`,

and `-576/323 + 16 = 4592/323`, so the whole monomial is

  `12 · (1 + d)² · chiSupAbs² · (chiSmallDecay 48)² · 2^96 · (μa³)^{4592/323}`.

The only thing left is `12(1+d)² ≤ 48`, i.e. `d ≤ 1` for `μa³ ≤ 1`.  This module
performs exactly that bookkeeping (the `(μa³)^{4592/323} → 0` window is supplied
by `rpow_window`, see `banddecay_window`).
-/

namespace Work.BoseFixB1.WB

theorem banddecay_alg {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    12 * (1 + Work.BoseBox.fsXp t 6) ^ 2
        * Submission.BoseGases.chiSmallBandDecay 48 (Work.BoseBox.fsXp t 6)
        * 2 ^ 96 * t ^ (16 : ℝ)
      ≤ (48 * Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * 2 ^ 96) * t ^ (4592 / 323 : ℝ) := by
  -- the `ℓd`-scale inverse power: `((fsXp t 6)⁻¹)^96 = t^{-576/323}`
  have h96 : ((Work.BoseBox.fsXp t 6)⁻¹) ^ (96 : ℕ) = t ^ ((-576 / 323 : ℝ)) := by
    rw [Work.BoseBox.fsXp_inv ht0 6, Work.BoseBox.fsXp_pow ht0.le (-6) 96]
    simp only [Work.BoseBox.fsXp]
    norm_num
  -- the exponent addition `-576/323 + 16 = 4592/323`
  have hpow : t ^ ((-576 / 323 : ℝ)) * t ^ (16 : ℝ) = t ^ (4592 / 323 : ℝ) := by
    rw [← Real.rpow_add ht0]
    congr 1
    norm_num
  -- the key identity: the band constant times `t^16` is the target monomial
  have hkey : Submission.BoseGases.chiSmallBandDecay 48 (Work.BoseBox.fsXp t 6) * t ^ (16 : ℝ)
      = Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * t ^ (4592 / 323 : ℝ) := by
    rw [Submission.BoseGases.chiSmallBandDecay]
    norm_num only [Nat.reduceMul]
    rw [h96]
    rw [show Submission.BoseGases.chiSupAbs ^ 2 * Submission.BoseGases.chiSmallDecay 48 ^ 2
          * t ^ ((-576 / 323 : ℝ)) * t ^ (16 : ℝ)
        = (Submission.BoseGases.chiSupAbs ^ 2 * Submission.BoseGases.chiSmallDecay 48 ^ 2)
          * (t ^ ((-576 / 323 : ℝ)) * t ^ (16 : ℝ)) by ring,
      hpow]
  -- the resulting right-hand factor is nonnegative
  have hXnn : 0 ≤ Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
      * t ^ (4592 / 323 : ℝ) :=
    mul_nonneg
      (mul_nonneg (pow_nonneg Submission.BoseGases.chiSupAbs_nonneg 2)
        (pow_nonneg (Submission.BoseGases.chiSmallDecay_nonneg 48) 2))
      (Real.rpow_nonneg ht0.le _)
  -- `d ≤ 1` gives `12 (1 + d)² ≤ 48`
  have h48 : 12 * (1 + Work.BoseBox.fsXp t 6) ^ 2 ≤ 48 := by
    have hle1 : Work.BoseBox.fsXp t 6 ≤ 1 := Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
    have hge : 0 ≤ Work.BoseBox.fsXp t 6 := (Work.BoseBox.fsXp_pos ht0).le
    nlinarith [sq_nonneg (Work.BoseBox.fsXp t 6)]
  calc
    12 * (1 + Work.BoseBox.fsXp t 6) ^ 2
        * Submission.BoseGases.chiSmallBandDecay 48 (Work.BoseBox.fsXp t 6)
        * 2 ^ 96 * t ^ (16 : ℝ)
        = (12 * (1 + Work.BoseBox.fsXp t 6) ^ 2)
            * (2 ^ 96 * (Submission.BoseGases.chiSmallBandDecay 48 (Work.BoseBox.fsXp t 6)
                * t ^ (16 : ℝ))) := by ring
    _ = (12 * (1 + Work.BoseBox.fsXp t 6) ^ 2)
            * (2 ^ 96 * (Submission.BoseGases.chiSupAbs ^ 2
                * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * t ^ (4592 / 323 : ℝ))) := by
          rw [hkey]
    _ ≤ 48 * (2 ^ 96 * (Submission.BoseGases.chiSupAbs ^ 2
            * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * t ^ (4592 / 323 : ℝ))) :=
          mul_le_mul_of_nonneg_right h48 (mul_nonneg (by norm_num) hXnn)
    _ = (48 * Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * 2 ^ 96) * t ^ (4592 / 323 : ℝ) := by ring

end Work.BoseFixB1.WB
