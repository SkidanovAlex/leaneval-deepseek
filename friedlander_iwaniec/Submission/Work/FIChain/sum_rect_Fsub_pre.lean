/-
# `Submission.Work.FIChain.sum_rect_Fsub_pre` — shared pointwise bounds for `sum_rect_Fsub_le`

This module collects the elementary pointwise bounds needed by the `sum_rect_Fsub_le` assembly
(`Submission/Work/FIChain/sum_rect_Fsub_le.lean`) and by the auxiliary integrability lemmas
`Work.FIChain.integrableOn_inner_Fsub` and `Work.FIChain.integrableOn_w_Fsub`.

* `Cm_mul_le_of_le_div`, `div_Cm_le_self` — the two elementary facts about `x/Cm` for `1 ≤ Cm`.
* `Fsub_abs_le_of_Cmw_le` — the uniform bound `|Fsub x Cm B ℓ v w| ≤ τ(ℓ)²·(x·4·Ã(x))` valid for
  *all* `v` as soon as `Cm·w ≤ x` (the `v ≤ x` indicator of `Fsub` kills the complement).
* `sum_Fsub_abs_le` — the same for the `ℓ`-sum over `Icc 1 x`.
* `Fsub_div_abs_le` — the divided form `|Fsub ℓ v w / (v·w)| ≤ K_ℓ / v` for `v > 0`, `w ≥ 1`.

NOTE for colleagues adding to this file: name any helper lemma you add with a prefix matching your
own file (e.g. `integrableOn_inner_Fsub_aux_...`) to avoid name clashes in `Work.FIChain`.
-/
import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj_le_defs

set_option autoImplicit false

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-- `w ≤ x/Cm` implies `Cm·w ≤ x` for `1 ≤ Cm`. -/
lemma Cm_mul_le_of_le_div (x Cm : ℕ) (hCm1 : 1 ≤ Cm) {w : ℝ} (hw : w ≤ (x : ℝ) / (Cm : ℝ)) :
    (Cm : ℝ) * w ≤ (x : ℝ) := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  calc (Cm : ℝ) * w ≤ (Cm : ℝ) * ((x : ℝ) / (Cm : ℝ)) :=
        mul_le_mul_of_nonneg_left hw hCmpos.le
    _ = (x : ℝ) := by field_simp

/-- `x/Cm ≤ x` for `1 ≤ Cm`. -/
lemma div_Cm_le_self (x Cm : ℕ) (hCm1 : 1 ≤ Cm) : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  rw [div_le_iff₀ hCmpos]
  nlinarith [Nat.cast_nonneg (α := ℝ) x,
    (by exact_mod_cast hCm1 : (1 : ℝ) ≤ (Cm : ℝ))]

/-- **Uniform pointwise bound for one `ℓ`-term of the joint rectangle integrand.**
For `Cm·w ≤ x` the bound `|Fsub x Cm B ℓ v w| ≤ τ(ℓ)²·(x·4·Ã(x))` holds for *all* `v`: if `v ≤ x`
this is `abs_Fsub_le`, and if `x < v` the defining indicator of `Fsub` fails. -/
lemma Fsub_abs_le_of_Cmw_le (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (v w : ℝ)
    (hCw : (Cm : ℝ) * w ≤ (x : ℝ)) :
    |Fsub x Cm B ℓ v w| ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) := by
  by_cases hvx : v ≤ (x : ℝ)
  · exact abs_Fsub_le x Cm B ℓ v w hvx hCw
  · rw [Fsub, if_neg (fun h => hvx h.2.2.2), abs_zero]
    have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
    positivity

/-- **Uniform pointwise bound for the `ℓ`-sum of the rectangle integrand**: for `Cm·w ≤ x`,
`|Σ_{ℓ ≤ x} Fsub x Cm B ℓ v w| ≤ Σ_{ℓ ≤ x} τ(ℓ)²·(x·4·Ã(x))`. -/
lemma sum_Fsub_abs_le (x Cm : ℕ) (B : ℝ) (v w : ℝ) (hCw : (Cm : ℝ) * w ≤ (x : ℝ)) :
    |∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w|
      ≤ ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum (fun ℓ _ => Fsub_abs_le_of_Cmw_le x Cm B ℓ v w hCw))

/-- **Divided pointwise bound**: for `0 < v`, `1 ≤ w` and `Cm·w ≤ x`,
`|Fsub x Cm B ℓ v w / (v·w)| ≤ τ(ℓ)²·(x·4·Ã(x)) / v`. -/
lemma Fsub_div_abs_le (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) {v w : ℝ} (hv : 0 < v) (hw : 1 ≤ w)
    (hCw : (Cm : ℝ) * w ≤ (x : ℝ)) :
    |Fsub x Cm B ℓ v w / (v * w)|
      ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / v := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hK : 0 ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) := by positivity
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hvw : 0 < v * w := mul_pos hv hw0
  rw [abs_div, abs_of_pos hvw]
  refine le_trans (div_le_div_of_nonneg_right (Fsub_abs_le_of_Cmw_le x Cm B ℓ v w hCw) hvw.le) ?_
  exact div_le_div_of_nonneg_left hK hv (by nlinarith [hw, hv.le])

end

end Work.FIChain
