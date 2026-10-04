import Mathlib
import Submission.Work.Diff.C.geoCrux.rauch_B_large
import Submission.Work.Diff.C.geoCrux.rauch_B_mid
import Submission.Work.Diff.C.geoCrux.rauch_B_tiny
import Submission.Work.Diff.C.geoCrux.rauch_exp_seven_four
import Submission.Work.Diff.C.geoCrux.rauch_exp_rpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

theorem rauch_arith {c ε₁ A R s : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hA : A ≤ 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4))
    (hR : R ≤ 8 / c) (hR1 : 1 ≤ R) :
    Real.exp A * R ^ (c / 4) * s ≤ s + 40 * (Real.sqrt c + ε₁ * Real.pi) := by
  -- abbreviate the exponent `B` that dominates `A + (c/4) log R`
  set B := 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c)
    with hBdef
  -- `B` is nonnegative: both summands are.
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : 0 ≤ ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) := by positivity
    have h2 : 0 ≤ Real.log (8 / c) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hc]; linarith
    nlinarith
  -- the exponential factor is dominated by `exp B`
  have hK : Real.exp A * R ^ (c / 4) ≤ Real.exp B := by
    rw [hBdef]; exact rauch_exp_rpow_le hc hR hR1 hA
  -- `exp B - 1` is at most `40 √c`, by a three-case analysis on the size of `c`
  have hfin : Real.exp B - 1 ≤ 40 * Real.sqrt c := by
    rcases le_or_gt (1 / 16 : ℝ) c with h16 | h16
    · -- large `c`: `B ≤ 7 c ≤ 7/4`, and `40 √c ≥ 10 ≥ 7`
      have h7 : B ≤ 7 * c := by rw [hBdef]; exact rauch_B_large hc hc1 hε₁ hnum2 h16
      have hB74 : B ≤ 7 / 4 := by linarith
      have hexp : Real.exp B ≤ 7 := le_trans (Real.exp_le_exp_of_le hB74) rauch_exp_seven_four
      have hs16 : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt c := by
        have := Real.sqrt_le_sqrt h16; rwa [hs16] at this
      linarith [Real.exp_pos B]
    · rcases le_or_gt (1 / 121 : ℝ) c with h121 | h121
      · -- medium `c`: `B ≤ 12 c ≤ 3/4 ≤ 1`, so `exp B - 1 ≤ 2 B ≤ 40 √c`
        have h12 : B ≤ 12 * c := by rw [hBdef]; exact rauch_B_mid hc hc1 hε₁ hnum2 h121
        have hB1 : B ≤ 1 := by linarith
        have habs : |Real.exp B - 1| ≤ 2 * B := by
          have h := Real.abs_exp_sub_one_le (show |B| ≤ 1 by rwa [abs_of_nonneg hBnn])
          rwa [abs_of_nonneg hBnn] at h
        have hle : Real.exp B - 1 ≤ 2 * B := le_trans (le_abs_self _) habs
        have hs121 : Real.sqrt (1 / 121 : ℝ) = 1 / 11 := by
          rw [show (1 / 121 : ℝ) = (1 / 11) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hsqrt : (1 / 11 : ℝ) ≤ Real.sqrt c := by
          have := Real.sqrt_le_sqrt h121; rwa [hs121] at this
        linarith
      · -- small `c`: `B ≤ 10.05 √c ≤ 1`, so `exp B - 1 ≤ 2 B ≤ 40 √c`
        have h10 : B ≤ 10.05 * Real.sqrt c := by
          rw [hBdef]; exact rauch_B_tiny hc hc1 hε₁ hnum2
        have hs121 : Real.sqrt (1 / 121 : ℝ) = 1 / 11 := by
          rw [show (1 / 121 : ℝ) = (1 / 11) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hsqrt_l : Real.sqrt c ≤ 1 / 11 := by
          have := Real.sqrt_le_sqrt h121.le; rwa [hs121] at this
        have hB1 : B ≤ 1 := by nlinarith
        have habs : |Real.exp B - 1| ≤ 2 * B := by
          have h := Real.abs_exp_sub_one_le (show |B| ≤ 1 by rwa [abs_of_nonneg hBnn])
          rwa [abs_of_nonneg hBnn] at h
        have hle : Real.exp B - 1 ≤ 2 * B := le_trans (le_abs_self _) habs
        linarith
  have hKnn : 0 ≤ Real.exp A * R ^ (c / 4) := by positivity
  -- multiply by `0 ≤ s ≤ 1`: `K s ≤ s + (exp B - 1)`
  have hKs : Real.exp A * R ^ (c / 4) * s ≤ s + (Real.exp B - 1) := by
    rcases le_or_gt (Real.exp A * R ^ (c / 4)) 1 with h | h
    · have h1 : Real.exp A * R ^ (c / 4) * s ≤ s := by nlinarith
      have h2 : 0 ≤ Real.exp B - 1 := by have := Real.one_le_exp hBnn; linarith
      linarith
    · have h3 : Real.exp A * R ^ (c / 4) * s ≤ s + (Real.exp A * R ^ (c / 4) - 1) := by
        nlinarith
      linarith
  have hep : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
  linarith

end Work.Diff.C.geoCrux
