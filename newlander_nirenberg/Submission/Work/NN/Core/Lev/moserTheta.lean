import Mathlib
import Submission.Work.NN.Core.CnPert

/-!
# The Moser exponent ratio `(2n)'`

One Gagliardo–Nirenberg step on `ℂⁿ ≃ ℝ^{2n}` replaces a Lebesgue exponent `p` by
`p · (2n)'` where `(2n)' = 2n/(2n-1)` is the conjugate exponent of `2n = dim_ℝ ℂⁿ`.  This file
fixes the notation `Work.NN.Core.Lev.moserTheta n` for it and records the two facts needed by the
Moser iteration: `1 < moserTheta n` (so the exponents grow geometrically) and the bridge to the
`ℝ≥0∞`-valued exponent used by `MeasureTheory.eLpNorm`.
-/

namespace Work.NN.Core.Lev

/-- `(2n)' = 2n/(2n-1)`, the conjugate exponent of `2n`, i.e. the factor by which one
Gagliardo–Nirenberg step multiplies the Lebesgue exponent. -/
noncomputable def moserTheta (n : ℕ) : ℝ := ((NNReal.conjExponent (2 * n) : NNReal) : ℝ)

/-- `ENNReal.ofReal (moserTheta n)` is the `ℝ≥0∞`-valued conjugate exponent of `2n`. -/
theorem ofReal_moserTheta (n : ℕ) :
    ENNReal.ofReal (moserTheta n) = ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal) := by
  rw [moserTheta, ENNReal.ofReal_coe_nnreal]

theorem one_lt_moserTheta {n : ℕ} (hn : 0 < n) : 1 < moserTheta n := by
  have hp1 : (1 : NNReal) < (2 * n : ℕ) := by
    rw [← NNReal.coe_lt_coe]
    have : (1 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  have hc : Real.HolderConjugate (((2 * n : ℕ) : NNReal) : ℝ) (moserTheta n) := by
    have := NNReal.HolderConjugate.coe (NNReal.HolderConjugate.conjExponent hp1)
    simpa [moserTheta] using this
  have hpos : (0 : ℝ) < (((2 * n : ℕ) : NNReal) : ℝ) - 1 := by
    have : (1 : ℝ) < (((2 * n : ℕ) : NNReal) : ℝ) := by exact_mod_cast hp1
    linarith
  rw [hc.conjugate_eq]
  rw [one_lt_div hpos]
  have : (((2 * n : ℕ) : NNReal) : ℝ) = (2 * n : ℝ) := by push_cast; ring
  rw [this]; linarith

theorem moserTheta_pos {n : ℕ} (hn : 0 < n) : 0 < moserTheta n :=
  lt_trans zero_lt_one (one_lt_moserTheta hn)

theorem moserTheta_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ moserTheta n := (moserTheta_pos hn).le

end Work.NN.Core.Lev
