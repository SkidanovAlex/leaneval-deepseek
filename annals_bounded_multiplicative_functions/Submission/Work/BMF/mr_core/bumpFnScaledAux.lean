import Mathlib
import Submission.Work.BMF.smoothing_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary facts about the rescaled bump function `t ↦ φ(t/A)`

`Work.BMF.bumpFn` is the smooth bump of `Submission/Work/BMF/smoothing_exists.lean`: it is
`1` on `[1/2, 2]` and vanishes identically outside `[1/4, 4]`.

This file collects the elementary facts about the *rescaled* function `t ↦ (φ(t/A) : ℂ)` which
are needed by the Abel-summation computation of the smoothed `Λ`-sum:

* `exp 4 ≤ A` (equivalently `1 < A`) when `A > 0` and `4 ≤ log A`;
* the derivative of `t ↦ (φ(t/A) : ℂ)` is `t ↦ ((φ'(t/A) : ℝ) : ℂ) / A`, and this is continuous
  (`φ` is `C¹`);
* `φ(t/A) = 0` for `t ≤ A/4` and for `4A ≤ t` (in particular at `t = ⌈4A⌉₊`).

Note: the hypothesis `4 ≤ Real.log A` alone does **not** imply `A > 0`, because Mathlib's
`Real.log` is even (`Real.log_neg_eq_log`).  Every statement below which needs positivity of `A`
carries it explicitly.
-/

namespace Work.BMF.mr_core

open MeasureTheory intervalIntegral

noncomputable section

section pos

variable {A : ℝ}

/-- `4 ≤ log A` and `A > 0` force `exp 4 ≤ A`. -/
lemma exp_four_le_of_pos_of_four_le_log (hA0 : 0 < A) (hA : 4 ≤ Real.log A) :
    Real.exp 4 ≤ A :=
  (Real.le_log_iff_exp_le hA0).mp hA

/-- `4 ≤ log A` and `A > 0` force `A > 1`. -/
lemma one_lt_of_pos_of_four_le_log (hA0 : 0 < A) (hA : 4 ≤ Real.log A) : 1 < A :=
  (Real.log_pos_iff hA0.le).mp (by linarith)

/-- `4 * A ≤ ⌈4 * A⌉₊`. -/
lemma four_mul_le_ceil (A : ℝ) : 4 * A ≤ ((⌈4 * A⌉₊ : ℕ) : ℝ) := Nat.le_ceil _

/-- `⌈4 * A⌉₊ ≥ 1` when `A > 0`. -/
lemma one_le_ceil_four_mul {A : ℝ} (hA0 : 0 < A) : 1 ≤ ⌈4 * A⌉₊ :=
  Nat.ceil_pos.mpr (by linarith)

/-- `0 < ⌈4 * A⌉₊` when `A > 0`. -/
lemma ceil_four_mul_pos {A : ℝ} (hA0 : 0 < A) : 0 < ⌈4 * A⌉₊ :=
  Nat.ceil_pos.mpr (by linarith)

end pos

section deriv

/-- Derivative of the complexified rescaled bump function `t ↦ (φ(t/A) : ℂ)`. -/
lemma hasDerivAt_bumpFn_div (A : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((Work.BMF.bumpFn (t / A) : ℝ) : ℂ))
      ((((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u / A) (1 / A) t := by
    simpa using (hasDerivAt_id t).div_const A
  have h2 : HasDerivAt Work.BMF.bumpFn (deriv Work.BMF.bumpFn (t / A)) (t / A) :=
    ((Work.BMF.bumpFn_contDiff 1).differentiable (by norm_num) (t / A)).hasDerivAt
  have h3 : HasDerivAt (fun u : ℝ => Work.BMF.bumpFn (u / A))
      (deriv Work.BMF.bumpFn (t / A) * (1 / A)) t := by
    simpa [Function.comp_def] using h2.comp t h1
  have h4 : HasDerivAt (fun y : ℝ => ((Work.BMF.bumpFn (y / A) : ℝ) : ℂ))
      (((deriv Work.BMF.bumpFn (t / A) * (1 / A) : ℝ) : ℂ)) t := h3.ofReal_comp
  have h5 : ((deriv Work.BMF.bumpFn (t / A) * (1 / A) : ℝ) : ℂ)
      = (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) := by
    push_cast
    ring
  rw [h5] at h4
  exact h4

/-- The derivative of the complexified rescaled bump function. -/
lemma deriv_bumpFn_div (A : ℝ) :
    deriv (fun t : ℝ => ((Work.BMF.bumpFn (t / A) : ℝ) : ℂ))
      = fun t => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) := by
  funext t
  exact (hasDerivAt_bumpFn_div A t).deriv

/-- The derivative of `t ↦ (φ(t/A) : ℂ)` is continuous, `φ` being `C¹`. -/
lemma continuous_deriv_bumpFn_div (A : ℝ) :
    Continuous (fun t : ℝ => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) := by
  have hcd : Continuous (deriv Work.BMF.bumpFn) :=
    (Work.BMF.bumpFn_contDiff 1).continuous_deriv (by norm_num)
  exact (Complex.continuous_ofReal.comp (hcd.comp (continuous_id.div_const A))).div_const A

/-- `t ↦ (φ(t/A) : ℂ)` is continuous. -/
lemma continuous_bumpFn_div (A : ℝ) :
    Continuous (fun t : ℝ => ((Work.BMF.bumpFn (t / A) : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp
    ((Work.BMF.bumpFn_contDiff 0).continuous.comp (continuous_id.div_const A))

/-- `t ↦ (φ(t/A) : ℂ)` is differentiable everywhere. -/
lemma differentiableAt_bumpFn_div (A : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => ((Work.BMF.bumpFn (t / A) : ℝ) : ℂ)) t :=
  (hasDerivAt_bumpFn_div A t).differentiableAt

end deriv

section zero

/-- `φ(t/A) = 0` when `4A ≤ t` and `A > 0`. -/
lemma bumpFn_div_eq_zero_of_four_mul_le {A t : ℝ} (hA : 0 < A) (ht : 4 * A ≤ t) :
    Work.BMF.bumpFn (t / A) = 0 := by
  rw [Work.BMF.bumpFn_eq_zero _ (Or.inr ?_)]
  rw [le_div_iff₀ hA]
  linarith

/-- `φ(t/A) = 0` when `t ≤ A/4` and `A > 0`. -/
lemma bumpFn_div_eq_zero_of_le {A t : ℝ} (hA : 0 < A) (ht : t ≤ A / 4) :
    Work.BMF.bumpFn (t / A) = 0 := by
  rw [Work.BMF.bumpFn_eq_zero _ (Or.inl ?_)]
  rw [div_le_iff₀ hA]
  linarith

/-- `φ (⌈4A⌉₊ / A) = 0` when `A > 0` (the upper summation limit lies beyond the support). -/
lemma bumpFn_div_ceil_eq_zero {A : ℝ} (hA : 0 < A) :
    Work.BMF.bumpFn (((⌈4 * A⌉₊ : ℕ) : ℝ) / A) = 0 :=
  bumpFn_div_eq_zero_of_four_mul_le hA (four_mul_le_ceil A)

end zero

end

end Work.BMF.mr_core
