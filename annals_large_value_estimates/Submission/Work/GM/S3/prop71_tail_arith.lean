import Mathlib
import Submission.Work.GM.S3.prop71_defs

namespace Work.GM.S3

open Submission.LargeValues

/-- Real-power arithmetic for the `O(T^{-200})` error term of GM Prop 7.1: with `T = M N = N^{6/5}`
and `j η ≥ 133/6`, the crude error

`N³ · (2 T)³ · (T^η)^{-j} = 8 · N³ · T³ · T^{-jη}`

is at most `C · N^{-20}` for all `N ≥ 1` (exponent check:
`3 + 3·(6/5) - (6/5)·jη ≤ 33/5 - 133/5 = -20`, so `C = 8` works).

This is exactly the step where one chooses `j` (the number of integrations by parts) as
`j = ⌈133/(6η)⌉` in GM Prop 7.1 to absorb the `|W|³ ≤ (2T)³` factor.

Proof route: `M N = (N:ℝ)^(6/5:ℝ)` (by definition), `Real.rpow_mul`, `Real.rpow_neg`,
`Real.rpow_le_rpow_of_exponent_le` (with base `N ≥ 1` and exponent `≤ -20`). -/
theorem prop71_tail_arith (η : ℝ) (hη : 0 < η) (j : ℕ)
    (hj : (133 : ℝ) / 6 ≤ (j : ℝ) * η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ^ 3 * (2 * Submission.LargeValues.M N) ^ 3 *
        (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) ≤
        C * (N : ℝ) ^ (-20 : ℤ) := by
  have _hηpos : (0 : ℝ) < η := hη
  refine ⟨8, by norm_num, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM : Submission.LargeValues.M N = (N : ℝ) ^ (6 / 5 : ℝ) := rfl
  rw [hM]
  -- `e1`, `e2`, `e3` convert the natural/iterated powers into a single real power of `N`.
  have e1 : (N : ℝ) ^ 3 = (N : ℝ) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast (N : ℝ) 3).symm
  have e2 : ((N : ℝ) ^ (6 / 5 : ℝ)) ^ 3 = (N : ℝ) ^ ((6 / 5 : ℝ) * ((3 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (6 / 5 : ℝ)) 3,
      ← Real.rpow_mul hN0 (6 / 5 : ℝ) ((3 : ℕ) : ℝ)]
  have e3 : (((N : ℝ) ^ (6 / 5 : ℝ)) ^ η) ^ (-(j : ℝ)) =
      (N : ℝ) ^ (((6 / 5 : ℝ) * η) * (-(j : ℝ))) := by
    rw [← Real.rpow_mul hN0 (6 / 5 : ℝ) η,
      ← Real.rpow_mul hN0 ((6 / 5 : ℝ) * η) (-(j : ℝ))]
  have hmain : (N : ℝ) ^ 3 * (2 * (N : ℝ) ^ (6 / 5 : ℝ)) ^ 3 *
        (((N : ℝ) ^ (6 / 5 : ℝ)) ^ η) ^ (-(j : ℝ))
      = 8 * (N : ℝ) ^ ((((3 : ℕ) : ℝ) + (6 / 5 : ℝ) * ((3 : ℕ) : ℝ)) +
          (((6 / 5 : ℝ) * η) * (-(j : ℝ)))) := by
    rw [show (2 * (N : ℝ) ^ (6 / 5 : ℝ)) ^ 3 = 8 * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ 3 by ring]
    rw [show (N : ℝ) ^ 3 * (8 * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ 3) *
            (((N : ℝ) ^ (6 / 5 : ℝ)) ^ η) ^ (-(j : ℝ))
          = 8 * ((N : ℝ) ^ 3 * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ 3 *
              (((N : ℝ) ^ (6 / 5 : ℝ)) ^ η) ^ (-(j : ℝ))) by ring]
    rw [e1, e2, e3]
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  rw [hmain]
  have hEc : (((3 : ℕ) : ℝ) + (6 / 5 : ℝ) * ((3 : ℕ) : ℝ)) +
        (((6 / 5 : ℝ) * η) * (-(j : ℝ))) ≤ ((-20 : ℤ) : ℝ) := by
    have h2 : (133 : ℝ) / 5 ≤ (6 / 5 : ℝ) * ((j : ℝ) * η) := by nlinarith [hj]
    push_cast
    nlinarith [h2]
  calc (8 : ℝ) * (N : ℝ) ^ ((((3 : ℕ) : ℝ) + (6 / 5 : ℝ) * ((3 : ℕ) : ℝ)) +
          (((6 / 5 : ℝ) * η) * (-(j : ℝ))))
      ≤ 8 * (N : ℝ) ^ ((-20 : ℤ) : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hN1 hEc
        linarith
    _ = 8 * (N : ℝ) ^ (-20 : ℤ) := by rw [Real.rpow_intCast]

end Work.GM.S3
