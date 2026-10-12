import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Defs
import Submission.Work.BoseB7A.smallness_conj8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.arith_aKH_log_div_dsell_le` — the `aK_H(1+log K_H)/(dsℓ)` ratio `≤ 1`

At FS's parameter point (`FSParamsView E`, diluteness `t = μa³ ≤ 2^{-323}`, so
`X = (μa³)^{1/323} ≤ 1/2`) the quantity `a·K_H·(1 + log K_H)/(d·s·ℓ)` is a
*decreasing* function of the diluteness and is `≤ 1`:

* `a/ℓ = a(μa)^{1/2}/K_ℓ = (μa³)^{1/2}/K_ℓ = X^{163}` (`smallness_conj8`), so with
  `K_H = X^{-549/4}`, `d = X⁶`, `s = X`,
  `a·K_H/(d·s·ℓ) = X^{163-549/4-7} = X^{75/4}`;
* `log K_H = (549/4)·log(1/X)`, and `X·log(1/X) ≤ 1`, giving
  `X^{75/4}·log(1/X) ≤ X^{71/4}`.

Hence LHS `≤ X^{75/4} + (549/4)X^{71/4}`, and since `X ≤ 1/2` this is at most
`2^{-18} + (549/4)·2^{-17} = 551/524288 ≤ 1`.

The first step is the already-proved lemma `Work.BoseB7A.smallness_conj8`.
-/

noncomputable section

namespace Work.BoseB7A

open Work.BoseB7 Work.BoseBox

theorem arith_aKH_log_div_dsell_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (ht : hv.t ≤ (1 / 2) ^ 323) :
    E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH) ≤ 1 := by
  have ht0 : 0 < hv.t := hv.t_pos
  -- `X = (μa³)^{1/323} ≤ 1/2`, from `μa³ ≤ 2^{-323}`
  have hX : fsXp hv.t 1 ≤ 1 / 2 := by
    have h2 : ((1 / 2 : ℝ) ^ 323) ^ (1 / 323 : ℝ) = 1 / 2 := by
      rw [← Real.rpow_natCast (1 / 2 : ℝ) 323,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        show ((323 : ℕ) : ℝ) * (1 / 323) = 1 by norm_num, Real.rpow_one]
    have h3 : hv.t ^ (1 / 323 : ℝ) ≤ ((1 / 2 : ℝ) ^ 323) ^ (1 / 323 : ℝ) :=
      Real.rpow_le_rpow ht0.le ht (by norm_num)
    simp only [fsXp]
    exact le_trans h3 (le_of_eq h2)
  have hmain := smallness_conj8 E hv (by norm_num : (1 / 2 : ℝ) ≤ 1) hX
  -- the numerical end: `2^{-75/4} + (549/4)·2^{-71/4} ≤ 1`
  have hnum : (1 / 2 : ℝ) ^ (75 / 4 : ℝ) + (549 / 4) * (1 / 2 : ℝ) ^ (71 / 4 : ℝ) ≤ 1 := by
    have h1 : (1 / 2 : ℝ) ^ (75 / 4 : ℝ) ≤ ((1 / 2 : ℝ) ^ 18 : ℝ) := by
      rw [← Real.rpow_natCast (1 / 2 : ℝ) 18]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have h2 : (1 / 2 : ℝ) ^ (71 / 4 : ℝ) ≤ ((1 / 2 : ℝ) ^ 17 : ℝ) := by
      rw [← Real.rpow_natCast (1 / 2 : ℝ) 17]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have h3 : (549 / 4) * (1 / 2 : ℝ) ^ (71 / 4 : ℝ) ≤ (549 / 4) * ((1 / 2 : ℝ) ^ 17) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    calc (1 / 2 : ℝ) ^ (75 / 4 : ℝ) + (549 / 4) * (1 / 2 : ℝ) ^ (71 / 4 : ℝ)
        ≤ ((1 / 2 : ℝ) ^ 18 : ℝ) + (549 / 4) * ((1 / 2 : ℝ) ^ 17) := add_le_add h1 h3
      _ ≤ 1 := by norm_num
  calc E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH)
      = E.aScat * E.KH * (1 + Real.log E.KH) / (E.d * E.s * E.ell) := by ring
    _ ≤ (1 / 2 : ℝ) ^ (75 / 4 : ℝ) + (549 / 4) * (1 / 2 : ℝ) ^ (71 / 4 : ℝ) := hmain
    _ ≤ 1 := hnum

end Work.BoseB7A
