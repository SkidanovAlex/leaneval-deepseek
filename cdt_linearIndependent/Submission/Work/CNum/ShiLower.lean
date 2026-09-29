import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LogUpMSpecPos

/-!
# `Work.CNum.ShiLower` — positivity of the per-term mantissa `shi`

`Work.CNum.shi` is the mantissa of the upper bound of the `k`-th term of the logarithmic series
evaluated on a ball (see `Work.CNum.SerUpDefs`).  Its companion `Work.CNum.shiUpper` bounds it
from above by `2 ^ 60`; here we prove the complementary lower bound `1 ≤ shi`, which is exactly
the positivity hypothesis needed to apply `Work.CNum.LogUpMSpec_pos` to `shi`.

The only input is the state invariant `SerInv`, which supplies `0 ≤ pe` and, together with the
inequality `ρ ^ k ≤ m2r sg` (`ρ = srad x y e ≥ 0`), forces `0 ≤ sg`; every other term of `shi` is
nonnegative outright (`nrmUp` is a natural number plus one, `mulU` preserves nonnegativity, and
the constant is `4`).
-/

namespace Work.CNum

open Work.ANum

theorem ShiLower {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) {k : ℕ} (hk : k < Work.CNum.SERM) {px py pe sg : ℤ} (h : Work.CNum.SerInv x y e σ k px py pe sg) : 1 ≤ Work.CNum.shi x y σ e k px py pe sg := by
  obtain ⟨hpe0, -, hRk, -, -, -, -⟩ := h
  -- `m2r e ≥ 0`, hence `srad x y e ≥ 0`
  have heR : 0 ≤ m2r e := (m2r_nonneg_iff e).mpr he
  have hsrad0 : 0 ≤ srad x y e := add_nonneg (norm_nonneg _) heR
  -- `0 ≤ m2r sg`, hence `0 ≤ sg`
  have hsgR : 0 ≤ m2r sg := le_trans (pow_nonneg hsrad0 k) hRk
  have hsg : 0 ≤ sg := (m2r_nonneg_iff sg).mp hsgR
  -- `mulU` preserves nonnegativity
  have hmul : 0 ≤ mulU e sg := by
    have hprod : 0 ≤ e * sg := mul_nonneg he hsg
    have h1 : Int.ediv (-(e * sg)) SC ≤ 0 := by
      have hle : -(e * sg) ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_left (le_trans (Int.ediv_mul_le (-(e * sg)) SC_ne_zero) hle) SC_pos
    simp only [mulU]; linarith
  have hk1 : (0 : ℤ) ≤ ((k : ℤ) + 1) := by positivity
  have hprod : 0 ≤ ((k : ℤ) + 1) * mulU e sg := mul_nonneg hk1 hmul
  have hnrm : 1 ≤ nrmUp (SC + px) py := by
    simp only [nrmUp, sqUp]; omega
  simp only [shi]
  linarith

end Work.CNum
