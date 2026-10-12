import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.ChiSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Constants for the `conv3Small 48` polydisc lower bound (`Work.BoseFixB1S`)

Shared numeric constants for the target
`Work.BoseFixB1S.conv3Small_48_polydisc_lower`
(`Submission/Work/BoseFixB1S/conv3Small_48_polydisc_lower.lean`).

* `conv48L := 1 - (1/2)·(3.1416 · 5/96)²  = 126286519/128000000` — the lower bound
  for `zeta1d` on the coordinate polydisc `|s| ≤ 5/96`, obtained from
  `cos x ≥ 1 - x²/2` (`Real.one_sub_sq_div_two_le_cos`) together with `π ≤ 3.1416`
  (`Real.pi_lt_d20`).
* `zeta1d_ge_conv48L` — that bound.

The choice of the numbers: on the cube `K = {|y_j - z_j/2| ≤ 1/48}` (whose volume is
`(1/24)³ = 1/13824`) both `y_j` and `(z-y)_j` range in `|·| ≤ 1/96·5`, so
`chiSmallBase 48 y · chiSmallBase 48 (z-y) ≥ conv48L^{288}` there; since
`conv48L^{288} ≥ 1/81` (`chiSmallNormSq 48 ≤ 1/343` supplies the other factor), the
product `conv48L^{288}/13824` gives `conv3Small 48 z ≥ 343/(81·13824) ≈ 3.06·10⁻⁴`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false

/-- `L = 1 - (1/2)·(3.1416·5/96)²`: the `zeta1d` lower bound on the coordinate
polydisc `|s| ≤ 5/96`. -/
def conv48L : ℝ := 126286519 / 128000000

lemma conv48L_nonneg : 0 ≤ conv48L := by norm_num [conv48L]

lemma conv48L_pos : 0 < conv48L := by norm_num [conv48L]

lemma conv48L_le_one : conv48L ≤ 1 := by norm_num [conv48L]

/-- `cos (π s) ≥ L` on `|s| ≤ 5/96` (`π ≤ 3.1416` and `cos x ≥ 1 - x²/2`). -/
theorem zeta1d_ge_conv48L (s : ℝ) (hs : |s| ≤ 5 / 96) : conv48L ≤ zeta1d s := by
  have hs12 : |s| ≤ 1 / 2 := le_trans hs (by norm_num)
  rw [zeta1d_of_abs_le hs12, cos_pi_mul_eq_cos_pi_abs s]
  have hpi : Real.pi ≤ 3.1416 := by
    have h := Real.pi_lt_d20
    linarith
  have hbound : Real.pi * |s| ≤ 5 * 3.1416 / 96 := by
    calc Real.pi * |s| ≤ Real.pi * (5 / 96) :=
          mul_le_mul_of_nonneg_left hs Real.pi_nonneg
      _ ≤ 3.1416 * (5 / 96) := mul_le_mul_of_nonneg_right hpi (by norm_num)
      _ = 5 * 3.1416 / 96 := by ring
  have hx0 : 0 ≤ Real.pi * |s| := mul_nonneg Real.pi_nonneg (abs_nonneg s)
  have hsq : (Real.pi * |s|) ^ 2 / 2 ≤ (5 * 3.1416 / 96) ^ 2 / 2 := by
    have h := pow_le_pow_left₀ hx0 hbound 2
    linarith
  have hcos : 1 - (5 * 3.1416 / 96) ^ 2 / 2 ≤ Real.cos (Real.pi * |s|) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi * |s|)
    linarith
  have hL : conv48L = 1 - (5 * 3.1416 / 96) ^ 2 / 2 := by
    norm_num [conv48L]
  rw [hL]
  exact hcos

/-- `conv48L ^ 288 ≥ 1/81`: from `log conv48L ≥ -(1/72)` (i.e. `(1-L)/L ≤ 1/72`,
the `log x ≤ x - 1` bound) and `exp 4 ≤ 81` (`exp 1 < 3`). -/
lemma conv48L_pow288_ge : (1 / 81 : ℝ) ≤ conv48L ^ 288 := by
  have hL : 0 < conv48L := conv48L_pos
  have hlog : -(1 / 72 : ℝ) ≤ Real.log conv48L := by
    have hinv : 0 < conv48L⁻¹ := inv_pos.mpr hL
    have h1 : Real.log conv48L⁻¹ ≤ conv48L⁻¹ - 1 := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_inv] at h1
    have h2 : conv48L⁻¹ - 1 ≤ (1 : ℝ) / 72 := by
      have heq : conv48L⁻¹ - 1 = (1 - conv48L) / conv48L := by
        rw [eq_div_iff (ne_of_gt hL), sub_mul, inv_mul_cancel₀ (ne_of_gt hL)]
        ring
      rw [heq, div_le_iff₀ hL]
      norm_num [conv48L]
    linarith
  have hpow : conv48L ^ 288 = Real.exp (288 * Real.log conv48L) := by
    rw [eq_comm, ← Real.exp_log (pow_pos hL 288), Real.log_pow]
    norm_num
  have hexp4 : Real.exp (-4 : ℝ) ≤ Real.exp (288 * Real.log conv48L) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h81 : (1 : ℝ) / 81 ≤ (Real.exp 4)⁻¹ := by
    have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      simpa using Real.exp_nat_mul 1 4
    have hlt : Real.exp 4 < 81 := by
      rw [h4]
      calc (Real.exp 1) ^ 4 < 3 ^ 4 :=
            pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
        _ = 81 := by norm_num
    have h := one_div_le_one_div_of_le (Real.exp_pos 4) hlt.le
    simpa [one_div] using h
  calc (1 / 81 : ℝ) ≤ (Real.exp 4)⁻¹ := h81
    _ = Real.exp (-4) := by rw [Real.exp_neg]
    _ ≤ Real.exp (288 * Real.log conv48L) := hexp4
    _ = conv48L ^ 288 := hpow.symm

end Work.BoseFixB1S
