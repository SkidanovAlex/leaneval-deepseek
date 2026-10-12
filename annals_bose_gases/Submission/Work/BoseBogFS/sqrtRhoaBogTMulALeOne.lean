import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBogFS.BogFSCompare
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-!
# `√(ρ·a v)·bogT v R μ·a v ≤ 1`

At the honest parameter block the momentum cutoff is
`T = bogT v R μ = 10⁶(1 + log D^{-1})/ε`, where `D = dil v μ = μ(a v)³` is the diluteness.
The target is the elementary statement that `√(ρa)·T·a ≤ 1`, i.e. that the *momentum*
scale `√(ρa)T` is at most the inverse length `a^{-1}` set by the scattering length.

Only three fields of `Core` are needed:

* `hTup : T ≤ 2·10⁶(323/156)·D^{-1/1292}`,
* `hsqρa : √(ρa) ≤ √(11/10)·D^{1/2}/a v`,
* `hDs : D^{1/1292} ≤ 1/1024`  (the numeric core bound).

Multiplying the first two gives `√(11/10)·2·10⁶(323/156)·D^{645/1292}`, and
`D^{645/1292} = (D^{1/1292})^{645} ≤ (1/1024)^3` because `1/1024 ≤ 1` and `645 ≥ 3`.
The remaining factor `√(11/10)·2·10⁶(323/156)·(1/1024)³ ≤ 1` is a numeric identity.
Note that no diluteness threshold beyond `coreBound` is required: the estimate is uniform
over the whole `Core` region, because `hDs` alone already confines `D` far below `1`.
-/
theorem sqrtRhoaBogTMulALeOne {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Work.BoseBogFS.Core v R μ ρ) :
    Real.sqrt (ρ * _root_.BoseGases.a v) * Work.BoseBogFS.bogT v R μ * _root_.BoseGases.a v ≤ 1 := by
  have hD0 : 0 < Work.BoseFixR.dil v μ := hC.hD0
  have hTpos : 0 < Work.BoseBogFS.bogT v R μ := hC.hTpos
  -- `D^{1/2}·D^{-1/1292} ≤ (1/1024)^3`
  have hkey : Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2)
        * Work.BoseFixR.dil v μ ^ (-(1 / 1292 : ℝ)) ≤ (1 / 1024 : ℝ) ^ 3 := by
    have hr0 : 0 ≤ Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
    have h1 : Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2)
          * Work.BoseFixR.dil v μ ^ (-(1 / 1292 : ℝ))
        = Work.BoseFixR.dil v μ ^ ((645 : ℝ) / 1292) := by
      rw [← Real.rpow_add hD0]
      congr 1
      norm_num
    rw [h1]
    have h2 : Work.BoseFixR.dil v μ ^ ((645 : ℝ) / 1292)
        = (Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292)) ^ (645 : ℝ) := by
      rw [show (645 : ℝ) / 1292 = (1 / 1292) * (645 : ℝ) by norm_num, Real.rpow_mul hD0.le]
    rw [h2]
    calc (Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292)) ^ (645 : ℝ)
        ≤ (1 / 1024 : ℝ) ^ (645 : ℝ) := Real.rpow_le_rpow hr0 hC.hDs (by norm_num)
      _ = (1 / 1024 : ℝ) ^ (645 : ℕ) := Real.rpow_natCast _ _
      _ ≤ (1 / 1024 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 3 ≤ 645)
  -- the algebraic rearrangement of the product of the two bounds
  have hprod :
      (Real.sqrt (11 / 10) * Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
          * (2 * 10 ^ 6 * (323 / 156) * Work.BoseFixR.dil v μ ^ (-(1 / 1292 : ℝ)))
          * _root_.BoseGases.a v
        = Real.sqrt (11 / 10) * (2 * 10 ^ 6 * (323 / 156))
          * (Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2)
              * Work.BoseFixR.dil v μ ^ (-(1 / 1292 : ℝ))) := by
    have hane : _root_.BoseGases.a v ≠ 0 := ne_of_gt hav
    field_simp
  calc Real.sqrt (ρ * _root_.BoseGases.a v) * Work.BoseBogFS.bogT v R μ * _root_.BoseGases.a v
      ≤ (Real.sqrt (11 / 10) * Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
          * (2 * 10 ^ 6 * (323 / 156) * Work.BoseFixR.dil v μ ^ (-(1 / 1292 : ℝ)))
          * _root_.BoseGases.a v := by
        have hb : 0 ≤ Real.sqrt (11 / 10) * Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2)
            / _root_.BoseGases.a v :=
          div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hD0.le _)) hav.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hC.hsqρa hC.hTup (le_of_lt hTpos) hb) hav.le
    _ = Real.sqrt (11 / 10) * (2 * 10 ^ 6 * (323 / 156))
        * (Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 2)
            * Work.BoseFixR.dil v μ ^ (-(1 / 1292 : ℝ))) := hprod
    _ ≤ Real.sqrt (11 / 10) * (2 * 10 ^ 6 * (323 / 156)) * (1 / 1024 : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg (Real.sqrt_nonneg _) (by norm_num))
    _ ≤ 1 := by
        have hsqrt : Real.sqrt (11 / 10) ≤ 2 := by
          have h4 : Real.sqrt (4 : ℝ) = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]
            norm_num
          exact le_trans (Real.sqrt_le_sqrt (by norm_num)) h4.le
        have hcT : (0 : ℝ) ≤ 2 * 10 ^ 6 * (323 / 156) := by norm_num
        calc Real.sqrt (11 / 10) * (2 * 10 ^ 6 * (323 / 156)) * (1 / 1024 : ℝ) ^ 3
            ≤ 2 * (2 * 10 ^ 6 * (323 / 156)) * (1 / 1024 : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsqrt hcT) (by norm_num)
          _ ≤ 1 := by norm_num

end Work.BoseBogFS
