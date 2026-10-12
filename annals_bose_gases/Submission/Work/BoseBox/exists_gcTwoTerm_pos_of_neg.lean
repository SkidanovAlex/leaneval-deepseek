import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.GCBoxBound
import Submission.LhyIntegral
import Submission.LocPotential
import Submission.Work.ModeLatticeR3
import Submission.Work.SmallBoxTBWord.Defs
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.exists_gcTwoTerm_pos_of_neg`

With `a < 0` the grand-canonical two-term value
`gcTwoTerm a C s ρ = 4πaρ²·(−1 + (128/(15√π))·√(ρa³) − C·(ρa³)^s)`
is **positive for some `ρ > 0`**, for every error coefficient `C ≥ 0` and
every exponent `s : ℝ`.

This is the mirror image of the audit's per-state observation that the
genuine (`a > 0`) two-term value is what bounds the box energy: for a *negative*
`a` the prefactor `4πaρ²` is negative, the square-root term vanishes
(`√(ρa³) = 0` once `ρa³ < 0`), and positivity of `gcTwoTerm` therefore only
asks that the bracket

    −1 − C·(ρa³)^s

be negative.  For a negative base Mathlib's `Real.rpow` is
`x^s = |x|^s·cos(sπ)` (`Real.rpow_def_of_neg`), so writing `t := ρ|a|³ > 0`
the bracket is `−1 − C·t^s·cos(sπ)`, and it suffices to find `t > 0` with

    C·t^s·cos(sπ) > −1.

If `cos(sπ) ≥ 0` this holds for *every* `t`; otherwise one takes `t` making
`t^s` small — large `t` when `s < 0`, small `t` when `s > 0`, which the single
explicit choice `t := exp(−log M/s)` with `M := 1 + 2C(−cos(sπ))` achieves
(`t^s = M⁻¹`, and `C·cos(sπ)/M > −1` since `C·cos(sπ) < 1`).

The two helper lemmas are stated once here because both facts are used by the
`BoseBox` chapter: `rpow_eq_abs_rpow_mul_cos` is the `Real.rpow` dictionary for
negative bases, and `exists_mul_rpow_mul_cos_gt` is the elementary existence
statement above.
-/

set_option autoImplicit false

open scoped Real

namespace Work.BoseBox

/-- `Real.rpow` at a negative base: `x^y = |x|^y·cos(yπ)` (`x < 0`). -/
lemma rpow_eq_abs_rpow_mul_cos {x y : ℝ} (hx : x < 0) :
    x ^ y = |x| ^ y * Real.cos (y * π) := by
  rw [Real.rpow_def_of_neg hx, Real.rpow_def_of_pos (abs_pos.mpr (ne_of_lt hx)),
    Real.log_abs]

/-- For every `C ≥ 0` and every real exponent `s` there is `t > 0` with
`C·t^s·cos(sπ) > −1` (the bracket of `gcTwoTerm` at a negative base becomes
negative there). -/
lemma exists_mul_rpow_mul_cos_gt (C s : ℝ) (hC : 0 ≤ C) :
    ∃ t : ℝ, 0 < t ∧ -1 < C * (t ^ s * Real.cos (s * π)) := by
  by_cases hc : 0 ≤ Real.cos (s * π)
  · -- the bracket `−1 − C·t^s·cos(sπ)` is already negative for every `t`
    refine ⟨1, one_pos, ?_⟩
    rw [Real.one_rpow]
    nlinarith [mul_nonneg hC hc]
  · -- `cos(sπ) < 0`: choose `t` with `t^s = (1 + 2C(−cos(sπ)))⁻¹`
    have hc' : Real.cos (s * π) < 0 := lt_of_not_ge hc
    have hs : s ≠ 0 := by
      intro h
      rw [h, zero_mul, Real.cos_zero] at hc'
      norm_num at hc'
    set M : ℝ := 1 + 2 * C * (-Real.cos (s * π)) with hMdef
    have hMpos : 0 < M := by
      have h1 : 0 < -Real.cos (s * π) := neg_pos.mpr hc'
      rw [hMdef]
      nlinarith [mul_nonneg hC h1.le]
    refine ⟨Real.exp (-(Real.log M) / s), Real.exp_pos _, ?_⟩
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have hslog : -(Real.log M) / s * s = -(Real.log M) := by
      field_simp
    rw [hslog, Real.exp_neg, Real.exp_log hMpos]
    have hX : C * Real.cos (s * π) < 1 := by
      have h2 : C * Real.cos (s * π) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hc'.le
      linarith
    have hEq : C * (M⁻¹ * Real.cos (s * π)) = (C * Real.cos (s * π)) / M := by ring
    rw [hEq, lt_div_iff₀ hMpos, hMdef]
    linarith

/-- **The lemma of this file.** For a negative scattering-length parameter `a`,
every `C ≥ 0` and every exponent `s`, the grand-canonical two-term value
`gcTwoTerm a C s ρ` is positive for some `ρ > 0`. -/
theorem exists_gcTwoTerm_pos_of_neg {a C s : ℝ} (ha : a < 0) (hC : 0 ≤ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ 0 < Submission.BoseGases.gcTwoTerm a C s ρ := by
  obtain ⟨t, htpos, ht⟩ := exists_mul_rpow_mul_cos_gt C s hC
  -- write `a = -A` with `A > 0` and take `ρ := t/A³`, so `ρa³ = -t`
  obtain ⟨A, hApos, haeq⟩ : ∃ A : ℝ, 0 < A ∧ a = -A := ⟨-a, neg_pos.mpr ha, by ring⟩
  have hA3pos : 0 < A ^ 3 := pow_pos hApos 3
  have hA3ne : A ^ 3 ≠ 0 := ne_of_gt hA3pos
  have hρpos : 0 < t / A ^ 3 := div_pos htpos hA3pos
  refine ⟨t / A ^ 3, hρpos, ?_⟩
  have hrho : t / A ^ 3 * a ^ 3 = -t := by
    rw [haeq, show (-A) ^ 3 = -(A ^ 3) by ring, mul_neg, div_mul_cancel₀ t hA3ne]
  -- the square-root term vanishes, the power term is `t^s·cos(sπ)`
  have hsqrt : √(t / A ^ 3 * a ^ 3) = 0 := by
    rw [hrho]
    exact Real.sqrt_eq_zero_of_nonpos (by linarith)
  have hrpow : (t / A ^ 3 * a ^ 3) ^ s = t ^ s * Real.cos (s * π) := by
    rw [hrho, rpow_eq_abs_rpow_mul_cos (show -t < 0 by linarith), abs_neg, abs_of_pos htpos]
  -- the bracket is negative
  have hbr : -1 + 128 / (15 * √π) * √(t / A ^ 3 * a ^ 3) - C * (t / A ^ 3 * a ^ 3) ^ s < 0 := by
    rw [hsqrt, hrpow]
    simp only [mul_zero, add_zero]
    linarith
  -- and the prefactor is negative, so the product is positive
  have hpre : 4 * π * a * (t / A ^ 3) ^ 2 < 0 := by
    have h1 : 0 < 4 * π := by positivity
    have h2 : 0 < (t / A ^ 3) ^ 2 := pow_pos hρpos 2
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 ha) h2
  dsimp [Submission.BoseGases.gcTwoTerm]
  exact mul_pos_of_neg_of_neg hpre hbr

end Work.BoseBox
