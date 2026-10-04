import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted `ℓ²` norms at **integer** (possibly negative) exponents

`Work.Diff.STE.CSq s` is defined for `s : ℕ`.  The final bookkeeping of the `SymCalcStep8` pair
estimates needs the *same* family at negative exponents: the pairing

  `|L2re y W| ≤ √(CSq t (fourierCoeff y)) · √(CSq (-t) (fourierCoeff W))`

(introduced here as `Work.Diff.STE.B3.SymCalcStep8.CSqZ`) is exactly weighted Cauchy–Schwarz, and
one of the two indices has to be `≤ 0`.

The definition is the obvious one, using `zpow` on the (positive) weight `wt`:

  `CSqZ t c = ∑'_m (wt m : ℝ) ^ t * ‖c m‖ ^ 2`.

Since `wt m ≥ 1`, the family `CSqZ t` is decreasing in `t`: `CSqZ t c ≤ CSqZ t' c` for `t ≤ t'`.
In particular `CSqZ (-t) c ≤ CSqZ 0 c ≤ CSqZ s c` for `s ≥ 0`, and on the non-negative integers
`CSqZ` is `Work.Diff.STE.CSq` (`CSqZ_natCast`).

The exponent arithmetic used in the assembly: for the `k`-th commutator one splits
`|L2re y ([Λ^k,Φ] g)| ≤ √(CSqZ (k-1) ŷ) √(CSqZ (-(k-1)) ([Λ^k,Φ]g))` and needs
`CSqZ (-(k-1)) ([Λ^k,Φ] g) ≤ C CSqZ k ĝ`, which is the pairing form of "[Λ^k,Φ] is of order
`2k-1`".
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **integer-exponent weighted `ℓ²` norm** of a coefficient family:
`CSqZ t c = ∑'_m wt(m)^t ‖c m‖²`, where `wt m = 1 + Σ_i (m i)² ≥ 1`. -/
def CSqZ (t : ℤ) (c : (ι → ℤ) → ℂ) : ℝ :=
  ∑' m : ι → ℤ, (Work.Diff.STE.wt m) ^ t * ‖c m‖ ^ 2

/-- On non-negative exponents `CSqZ` is `Work.Diff.STE.CSq`. -/
theorem CSqZ_natCast (n : ℕ) (c : (ι → ℤ) → ℂ) :
    CSqZ (n : ℤ) c = Work.Diff.STE.CSq n c := by
  simp only [CSqZ, Work.Diff.STE.CSq, zpow_natCast]

/-- The weight is at least `1`. -/
theorem one_le_wt (m : ι → ℤ) : (1 : ℝ) ≤ Work.Diff.STE.wt m := by
  have h0 : (0 : ℝ) ≤ ∑ i, ((m i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [Work.Diff.STE.wt]
  linarith

/-- `CSqZ` is monotone in the exponent, **on summable families**.  The summability hypothesis is
needed because `tsum` is `0` on non-summable families, so the monotonicity statement is only
meaningful when the larger exponent is summable. -/
theorem CSqZ_mono {t t' : ℤ} (h : t ≤ t') (c : (ι → ℤ) → ℂ)
    (hs : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t' * ‖c m‖ ^ 2)) :
    CSqZ t c ≤ CSqZ t' c := by
  have hpt : ∀ m : ι → ℤ,
      (Work.Diff.STE.wt m) ^ t * ‖c m‖ ^ 2 ≤ (Work.Diff.STE.wt m) ^ t' * ‖c m‖ ^ 2 := by
    intro m
    have h1 : (Work.Diff.STE.wt m) ^ t ≤ (Work.Diff.STE.wt m) ^ t' :=
      zpow_le_zpow_right₀ (one_le_wt m) h
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hsmall : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t * ‖c m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (by linarith [one_le_wt m]) t) (sq_nonneg _))
      hpt hs
  exact Summable.tsum_le_tsum hpt hsmall hs

/-- `CSqZ t` is non-negative. -/
theorem CSqZ_nonneg (t : ℤ) (c : (ι → ℤ) → ℂ) : 0 ≤ CSqZ t c :=
  tsum_nonneg fun m => by
    have hz : (0 : ℝ) ≤ Work.Diff.STE.wt m := le_of_lt (Work.Diff.STE.wt_pos m)
    exact mul_nonneg (zpow_nonneg hz t) (sq_nonneg _)

end Work.Diff.STE.B3.SymCalcStep8
