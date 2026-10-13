/-
# `|D_θ^i Γ| ≤ 10⁷·Γ` on `Iθ`, for `i ≤ 8`

This extends `Work.FTS.LocData6.DthIter_Gam_abs_le6` (the case `i ≤ 6`, constant `10⁵`) by two
orders, to the order required by the order-`8` data of this chapter (`FTS_LocDatum3a`).

As in the three lower-order files, the statement is reduced through
`Work.Spaces.dthU_iter_Gam_abs_bound` to the coefficient bound `|Tfun j α θ| ≤ 10⁷` for
`j ≤ 7`.  Recall `Tfun j α θ = (Qp j α).eval (cos 2θ)` (`Work.FTS.LocData.Tfun_eq_Qp`), where
the coefficient polynomials obey `Qp 0 α = X - 1/3` and
`Qp (j+1) α = -2(1-X²)·(Qp j α)' + α·(X-1/3)·(Qp j α)`.

So it remains to bound `Tfun 6 α` and `Tfun 7 α`, i.e. `Qp 6 α` and `Qp 7 α` on `[-1,1]`.  The
bounds are propagated through the derivatives of the `Qp j`: writing
`B(j,k) = sup_{|v|≤1} |(Qp j α)^{(k)}(v)|`, differentiating the recursion `k` times gives

  `(Qp (j+1) α)^{(k)} = -2(1-X²)·(Qp j)^{(k+1)} + 4kX·(Qp j)^{(k)} + 4·C(k,2)·(Qp j)^{(k-1)}`
  `                          + α(X-1/3)·(Qp j)^{(k)} + αk·(Qp j)^{(k-1)}`

(`Qp_deriv3_succ_eval`, `Qp_deriv4_succ_eval`), hence the bound recursion

  `B(j+1,k) ≤ 2·B(j,k+1) + (4k + 4/3)·B(j,k) + (4·C(k,2) + k)·B(j,k-1)`,

using `|1-v²| ≤ 1`, `|v| ≤ 1`, `|v-1/3| ≤ 4/3` and `0 ≤ α ≤ 1`.  Starting from the bounds of
the lower-order files (`|Qp 2| ≤ 496/27`, `|(Qp 2)'| ≤ 154/3`, `|(Qp 2)''| ≤ 96`,
`|(Qp 2)'''| ≤ 90`, `|Qp 3| ≤ 10300/81`, `|(Qp 3)'| ≤ 13072/27`, `|(Qp 3)''| ≤ 1384`,
`|Qp 4| ≤ 276496/243`, `|(Qp 4)'| ≤ 443660/81`, `|Qp 5| ≤ 10⁵`) the chain closes:

  `B(3,3) ≤ 2640`, `B(3,4) ≤ 2520`, `B(4,2) ≤ 21103`, `B(4,3) ≤ 61000`, `B(5,1) ≤ 72557`,
  `B(5,2) ≤ 351830`, `B(6,0) ≤ 278500`, `B(6,1) ≤ 1190700`, `B(7,0) ≤ 2752800 ≤ 10⁷`.

The derivative orders stop increasing because `Qp 2` has degree `3`, so `(Qp 2)^{(4)} = 0`.
Everything rests on `[propext, Classical.choice, Quot.sound]` only.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_LocDatum3a

open Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Derivative recursions for the coefficient polynomials `Qp` -/

/-- The third derivative recursion for the coefficient polynomials, obtained by
differentiating `(Qp (j+1) α)' = 4v·(Qp j)' - 2(1-v²)·(Qp j)'' + α·Qp j + α(v-1/3)·(Qp j)'
twice (equivalently: the general `k`-th derivative recursion at `k = 3`). -/
theorem Qp_deriv3_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2) * (Qp j α).derivative.derivative.derivative.derivative.eval v
        + 12 * v * (Qp j α).derivative.derivative.derivative.eval v
        + 12 * (Qp j α).derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.derivative.derivative.eval v
        + 3 * α * (Qp j α).derivative.derivative.eval v := by
  simp [Qp]; ring

/-- The fourth derivative recursion (the general recursion at `k = 4`). -/
theorem Qp_deriv4_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2)
          * (Qp j α).derivative.derivative.derivative.derivative.derivative.eval v
        + 16 * v * (Qp j α).derivative.derivative.derivative.derivative.eval v
        + 24 * (Qp j α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.derivative.derivative.derivative.eval v
        + 4 * α * (Qp j α).derivative.derivative.derivative.eval v := by
  simp [Qp]; ring

/-- `Qp 2 α` has degree `3`, so its fourth derivative vanishes. -/
theorem Qp2_deriv4_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.derivative.derivative.eval v = 0 := by
  simp [Qp]

/-- `Qp 2 α` has degree `3`, so its fifth derivative vanishes. -/
theorem Qp2_deriv5_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v = 0 := by
  simp [Qp]

/-! ## The concrete recursions used below -/

/-- The recursion for `(Qp 3 α)'''`. -/
theorem Qp3_d3_eval (α v : ℝ) :
    (Qp 3 α).derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        + 12 * v * (Qp 2 α).derivative.derivative.derivative.eval v
        + 12 * (Qp 2 α).derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.eval v
        + 3 * α * (Qp 2 α).derivative.derivative.eval v :=
  Qp_deriv3_succ_eval 2 α v

/-- The recursion for `(Qp 3 α)''''`. -/
theorem Qp3_d4_eval (α v : ℝ) :
    (Qp 3 α).derivative.derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2)
          * (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v
        + 16 * v * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        + 24 * (Qp 2 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        + 4 * α * (Qp 2 α).derivative.derivative.derivative.eval v :=
  Qp_deriv4_succ_eval 2 α v

/-- The recursion for `(Qp 4 α)''`. -/
theorem Qp4_d2_eval (α v : ℝ) :
    (Qp 4 α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp 3 α).derivative.eval v
        + 8 * v * (Qp 3 α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.eval v :=
  Work.FTS.LocData6.Qp_deriv_deriv_succ_eval 3 α v

/-- The recursion for `(Qp 4 α)'''`. -/
theorem Qp4_d3_eval (α v : ℝ) :
    (Qp 4 α).derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.derivative.eval v
        + 12 * v * (Qp 3 α).derivative.derivative.derivative.eval v
        + 12 * (Qp 3 α).derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.derivative.eval v
        + 3 * α * (Qp 3 α).derivative.derivative.eval v :=
  Qp_deriv3_succ_eval 3 α v

/-- The recursion for `(Qp 5 α)'`. -/
theorem Qp5_d1_eval (α v : ℝ) :
    (Qp 5 α).derivative.eval v
      = 4 * v * (Qp 4 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.eval v
        + α * (Qp 4 α).eval v
        + α * (v - 1 / 3) * (Qp 4 α).derivative.eval v :=
  Work.FTS.LocDataExt.Qp_deriv_succ_eval 4 α v

/-- The recursion for `(Qp 5 α)''`. -/
theorem Qp5_d2_eval (α v : ℝ) :
    (Qp 5 α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp 4 α).derivative.eval v
        + 8 * v * (Qp 4 α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 4 α).derivative.derivative.eval v :=
  Work.FTS.LocData6.Qp_deriv_deriv_succ_eval 4 α v

/-- The recursion for `Qp 6 α`. -/
theorem Qp6_eval (α v : ℝ) :
    (Qp 6 α).eval v
      = -2 * (1 - v ^ 2) * (Qp 5 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 5 α).eval v :=
  Qp_succ_eval 5 α v

/-- The recursion for `(Qp 6 α)'`. -/
theorem Qp6_d1_eval (α v : ℝ) :
    (Qp 6 α).derivative.eval v
      = 4 * v * (Qp 5 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 5 α).derivative.derivative.eval v
        + α * (Qp 5 α).eval v
        + α * (v - 1 / 3) * (Qp 5 α).derivative.eval v :=
  Work.FTS.LocDataExt.Qp_deriv_succ_eval 5 α v

/-- The recursion for `Qp 7 α`. -/
theorem Qp7_eval (α v : ℝ) :
    (Qp 7 α).eval v
      = -2 * (1 - v ^ 2) * (Qp 6 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 6 α).eval v :=
  Qp_succ_eval 6 α v

/-! ## Assembling bounds from termwise bounds -/

/-- `|a + b| ≤ A + B` from termwise bounds. -/
theorem abs_sum_le2 {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a + b| ≤ A + B := by
  linarith [abs_add_le a b]

/-- `|a + b + c + d| ≤ A + B + C + D` from termwise bounds (left-associated sum). -/
theorem abs_sum_le4 {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) : |a + b + c + d| ≤ A + B + C + D := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `|a + b + c + d + e| ≤ A + B + C + D + E` from termwise bounds (left-associated sum). -/
theorem abs_sum_le5 {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E := by
  have h1 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h2 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h3 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h4 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `|α| ≤ 1` for `0 ≤ α ≤ 1`. -/
theorem abs_alpha_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |α| ≤ 1 := by
  rwa [abs_of_nonneg hα0]

/-- `|α·(v - 1/3)| ≤ 4/3` for `0 ≤ α ≤ 1` and `|v| ≤ 1`. -/
theorem abs_alpha_sub_third_le {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |α * (v - 1 / 3)| ≤ 4 / 3 :=
  (abs_mul_le_of (A := 1) (B := 4 / 3) (abs_alpha_le_one hα0 hα1) (abs_sub_third_le hv)
    (by norm_num)).trans (by norm_num)

/-! ## The chain of derivative bounds

Each statement bounds the `k`-th derivative of `Qp j α` on `|v| ≤ 1` uniformly for
`0 ≤ α ≤ 1`. -/

/-- `B(3,3)`: the third derivative of `Qp 3 α`. -/
theorem Qp3_deriv3_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.derivative.derivative.eval v| ≤ 2640 := by
  rw [Qp3_d3_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hT : |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 :=
    Work.FTS.LocData6.Qp2_deriv3_bound hα0 hα1
  have hU : |(Qp 2 α).derivative.derivative.eval v| ≤ 96 :=
    Work.FTS.LocDataExt.Qp2_deriv2_bound hα0 hα1 hv
  have h4 : (Qp 2 α).derivative.derivative.derivative.derivative.eval v = 0 :=
    Qp2_deriv4_eval α v
  have hA : |(-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v|
      ≤ 2 * 0 := by
    rw [h4, mul_zero, abs_zero]; norm_num
  have hB : |12 * v * (Qp 2 α).derivative.derivative.derivative.eval v| ≤ 12 * 90 := by
    rw [show 12 * v * (Qp 2 α).derivative.derivative.derivative.eval v
        = (12 * v) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 12) (B := 90)
      (by rw [abs_mul]; norm_num; exact hv) hT (by norm_num)
  have hC : |12 * (Qp 2 α).derivative.derivative.eval v| ≤ 12 * 96 :=
    abs_mul_le_of (A := 12) (B := 96) (by norm_num) hU (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.eval v|
      ≤ (4 / 3) * 90 := by
    rw [show α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 90)
      (abs_alpha_sub_third_le hα0 hα1 hv) hT (by norm_num)
  have hE : |3 * α * (Qp 2 α).derivative.derivative.eval v| ≤ 3 * 96 := by
    rw [show 3 * α * (Qp 2 α).derivative.derivative.eval v
        = (3 * α) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 3) (B := 96)
      (by rw [abs_mul]; norm_num; exact hαa) hU (by norm_num)
  have hsum := abs_sum_le5 hA hB hC hD hE
  linarith [hsum]

/-- `B(3,4)`: the fourth derivative of `Qp 3 α`. -/
theorem Qp3_deriv4_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.derivative.derivative.derivative.eval v| ≤ 2520 := by
  rw [Qp3_d4_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hT : |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 :=
    Work.FTS.LocData6.Qp2_deriv3_bound hα0 hα1
  have h4 : (Qp 2 α).derivative.derivative.derivative.derivative.eval v = 0 :=
    Qp2_deriv4_eval α v
  have h5 : (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v = 0 :=
    Qp2_deriv5_eval α v
  have hA : |(-2) * (1 - v ^ 2)
      * (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v| ≤ 2 * 0 := by
    rw [h5, mul_zero, abs_zero]; norm_num
  have hB : |16 * v * (Qp 2 α).derivative.derivative.derivative.derivative.eval v| ≤ 16 * 0 := by
    rw [show 16 * v * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        = (16 * v) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v by ring]
    rw [h4, mul_zero, abs_zero]; norm_num
  have hC : |24 * (Qp 2 α).derivative.derivative.derivative.eval v| ≤ 24 * 90 :=
    abs_mul_le_of (A := 24) (B := 90) (by norm_num) hT (by norm_num)
  have hD : |α * (v - 1 / 3)
      * (Qp 2 α).derivative.derivative.derivative.derivative.eval v| ≤ (4 / 3) * 0 := by
    rw [show α * (v - 1 / 3)
        * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        = (α * (v - 1 / 3))
          * (Qp 2 α).derivative.derivative.derivative.derivative.eval v by ring]
    rw [h4, mul_zero, abs_zero]; norm_num
  have hE : |4 * α * (Qp 2 α).derivative.derivative.derivative.eval v| ≤ 4 * 90 := by
    rw [show 4 * α * (Qp 2 α).derivative.derivative.derivative.eval v
        = (4 * α) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4) (B := 90)
      (by rw [abs_mul]; norm_num; exact hαa) hT (by norm_num)
  have hsum := abs_sum_le5 hA hB hC hD hE
  linarith [hsum]

/-- `B(4,2)`: the second derivative of `Qp 4 α`. -/
theorem Qp4_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).derivative.derivative.eval v| ≤ 21103 := by
  rw [Qp4_d2_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hS : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 :=
    Work.FTS.LocDataExt.Qp3_deriv_bound hα0 hα1 hv
  have hU : |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 :=
    Work.FTS.LocData6.Qp3_deriv2_bound hα0 hα1 hv
  have h3 : |(Qp 3 α).derivative.derivative.derivative.eval v| ≤ 2640 :=
    Qp3_deriv3_bound hα0 hα1 hv
  have hA : |(4 + 2 * α) * (Qp 3 α).derivative.eval v| ≤ 6 * (13072 / 27) :=
    abs_mul_le_of (A := 6) (B := 13072 / 27) h4 hS (by norm_num)
  have hB : |8 * v * (Qp 3 α).derivative.derivative.eval v| ≤ 8 * 1384 := by
    rw [show 8 * v * (Qp 3 α).derivative.derivative.eval v
        = (8 * v) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 8) (B := 1384)
      (by rw [abs_mul]; norm_num; exact hv) hU (by norm_num)
  have hC : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.eval v|
      ≤ 2 * 2640 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 2640)
      (by rw [abs_mul]; norm_num; exact h1) h3 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.eval v| ≤ (4 / 3) * 1384 := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 1384)
      (abs_alpha_sub_third_le hα0 hα1 hv) hU (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(4,3)`: the third derivative of `Qp 4 α`. -/
theorem Qp4_deriv3_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).derivative.derivative.derivative.eval v| ≤ 61000 := by
  rw [Qp4_d3_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hU : |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 :=
    Work.FTS.LocData6.Qp3_deriv2_bound hα0 hα1 hv
  have h3 : |(Qp 3 α).derivative.derivative.derivative.eval v| ≤ 2640 :=
    Qp3_deriv3_bound hα0 hα1 hv
  have h4 : |(Qp 3 α).derivative.derivative.derivative.derivative.eval v| ≤ 2520 :=
    Qp3_deriv4_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2)
      * (Qp 3 α).derivative.derivative.derivative.derivative.eval v| ≤ 2 * 2520 := by
    rw [show (-2) * (1 - v ^ 2)
          * (Qp 3 α).derivative.derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2))
          * (Qp 3 α).derivative.derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 2520)
      (by rw [abs_mul]; norm_num; exact h1) h4 (by norm_num)
  have hB : |12 * v * (Qp 3 α).derivative.derivative.derivative.eval v| ≤ 12 * 2640 := by
    rw [show 12 * v * (Qp 3 α).derivative.derivative.derivative.eval v
        = (12 * v) * (Qp 3 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 12) (B := 2640)
      (by rw [abs_mul]; norm_num; exact hv) h3 (by norm_num)
  have hC : |12 * (Qp 3 α).derivative.derivative.eval v| ≤ 12 * 1384 :=
    abs_mul_le_of (A := 12) (B := 1384) (by norm_num) hU (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.derivative.eval v|
      ≤ (4 / 3) * 2640 := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 2640)
      (abs_alpha_sub_third_le hα0 hα1 hv) h3 (by norm_num)
  have hE : |3 * α * (Qp 3 α).derivative.derivative.eval v| ≤ 3 * 1384 := by
    rw [show 3 * α * (Qp 3 α).derivative.derivative.eval v
        = (3 * α) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 3) (B := 1384)
      (by rw [abs_mul]; norm_num; exact hαa) hU (by norm_num)
  have hsum := abs_sum_le5 hA hB hC hD hE
  linarith [hsum]

/-- `B(5,1)`: the first derivative of `Qp 5 α`. -/
theorem Qp5_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 5 α).derivative.eval v| ≤ 72557 := by
  rw [Qp5_d1_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 :=
    Work.FTS.LocData6.Qp4_deriv_bound hα0 hα1 hv
  have hU : |(Qp 4 α).derivative.derivative.eval v| ≤ 21103 :=
    Qp4_deriv2_bound hα0 hα1 hv
  have hQ : |(Qp 4 α).eval v| ≤ 276496 / 243 :=
    Work.FTS.LocData6.Qp4_eval_bound_sharp hα0 hα1 hv
  have hA : |4 * v * (Qp 4 α).derivative.eval v| ≤ 4 * (443660 / 81) := by
    rw [show 4 * v * (Qp 4 α).derivative.eval v
        = (4 * v) * (Qp 4 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4) (B := 443660 / 81)
      (by rw [abs_mul]; norm_num; exact hv) hS (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.eval v| ≤ 2 * 21103 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 4 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 21103)
      (by rw [abs_mul]; norm_num; exact h1) hU (by norm_num)
  have hC : |α * (Qp 4 α).eval v| ≤ 1 * (276496 / 243) :=
    abs_mul_le_of (A := 1) (B := 276496 / 243) hαa hQ (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 4 α).derivative.eval v| ≤ (4 / 3) * (443660 / 81) := by
    rw [show α * (v - 1 / 3) * (Qp 4 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 4 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 443660 / 81)
      (abs_alpha_sub_third_le hα0 hα1 hv) hS (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(5,2)`: the second derivative of `Qp 5 α`. -/
theorem Qp5_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 5 α).derivative.derivative.eval v| ≤ 351830 := by
  rw [Qp5_d2_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hS : |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 :=
    Work.FTS.LocData6.Qp4_deriv_bound hα0 hα1 hv
  have hU : |(Qp 4 α).derivative.derivative.eval v| ≤ 21103 :=
    Qp4_deriv2_bound hα0 hα1 hv
  have h3 : |(Qp 4 α).derivative.derivative.derivative.eval v| ≤ 61000 :=
    Qp4_deriv3_bound hα0 hα1 hv
  have hA : |(4 + 2 * α) * (Qp 4 α).derivative.eval v| ≤ 6 * (443660 / 81) :=
    abs_mul_le_of (A := 6) (B := 443660 / 81) h4 hS (by norm_num)
  have hB : |8 * v * (Qp 4 α).derivative.derivative.eval v| ≤ 8 * 21103 := by
    rw [show 8 * v * (Qp 4 α).derivative.derivative.eval v
        = (8 * v) * (Qp 4 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 8) (B := 21103)
      (by rw [abs_mul]; norm_num; exact hv) hU (by norm_num)
  have hC : |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.derivative.eval v|
      ≤ 2 * 61000 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 4 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 61000)
      (by rw [abs_mul]; norm_num; exact h1) h3 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 4 α).derivative.derivative.eval v| ≤ (4 / 3) * 21103 := by
    rw [show α * (v - 1 / 3) * (Qp 4 α).derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 4 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 21103)
      (abs_alpha_sub_third_le hα0 hα1 hv) hU (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(6,0)`: `Qp 6 α` on `[-1,1]`. -/
theorem Qp6_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 6 α).eval v| ≤ 278500 := by
  rw [Qp6_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 5 α).derivative.eval v| ≤ 72557 := Qp5_deriv_bound hα0 hα1 hv
  have hQ : |(Qp 5 α).eval v| ≤ 100000 := Work.FTS.LocData6.Qp5_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 5 α).derivative.eval v| ≤ 2 * 72557 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 5 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 5 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 72557)
      (by rw [abs_mul]; norm_num; exact h1) hS (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 5 α).eval v| ≤ (4 / 3) * 100000 := by
    rw [show α * (v - 1 / 3) * (Qp 5 α).eval v
        = (α * (v - 1 / 3)) * (Qp 5 α).eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 100000)
      (abs_alpha_sub_third_le hα0 hα1 hv) hQ (by norm_num)
  have hsum := abs_sum_le2 hA hB
  linarith [hsum]

/-- `B(6,1)`: the first derivative of `Qp 6 α`. -/
theorem Qp6_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 6 α).derivative.eval v| ≤ 1190700 := by
  rw [Qp6_d1_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 5 α).derivative.eval v| ≤ 72557 := Qp5_deriv_bound hα0 hα1 hv
  have hU : |(Qp 5 α).derivative.derivative.eval v| ≤ 351830 := Qp5_deriv2_bound hα0 hα1 hv
  have hQ : |(Qp 5 α).eval v| ≤ 100000 := Work.FTS.LocData6.Qp5_eval_bound hα0 hα1 hv
  have hA : |4 * v * (Qp 5 α).derivative.eval v| ≤ 4 * 72557 := by
    rw [show 4 * v * (Qp 5 α).derivative.eval v
        = (4 * v) * (Qp 5 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4) (B := 72557)
      (by rw [abs_mul]; norm_num; exact hv) hS (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 5 α).derivative.derivative.eval v| ≤ 2 * 351830 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 5 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 5 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 351830)
      (by rw [abs_mul]; norm_num; exact h1) hU (by norm_num)
  have hC : |α * (Qp 5 α).eval v| ≤ 1 * 100000 :=
    abs_mul_le_of (A := 1) (B := 100000) hαa hQ (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 5 α).derivative.eval v| ≤ (4 / 3) * 72557 := by
    rw [show α * (v - 1 / 3) * (Qp 5 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 5 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 72557)
      (abs_alpha_sub_third_le hα0 hα1 hv) hS (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(7,0)`: `Qp 7 α` on `[-1,1]`. -/
theorem Qp7_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 7 α).eval v| ≤ 2752800 := by
  rw [Qp7_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 6 α).derivative.eval v| ≤ 1190700 := Qp6_deriv_bound hα0 hα1 hv
  have hQ : |(Qp 6 α).eval v| ≤ 278500 := Qp6_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 6 α).derivative.eval v| ≤ 2 * 1190700 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 6 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 6 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 1190700)
      (by rw [abs_mul]; norm_num; exact h1) hS (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 6 α).eval v| ≤ (4 / 3) * 278500 := by
    rw [show α * (v - 1 / 3) * (Qp 6 α).eval v
        = (α * (v - 1 / 3)) * (Qp 6 α).eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 278500)
      (abs_alpha_sub_third_le hα0 hα1 hv) hQ (by norm_num)
  have hsum := abs_sum_le2 hA hB
  linarith [hsum]

/-! ## The coefficient bound and the main theorem -/

/-- **The coefficient bound `|Tfun j α θ| ≤ 10⁷` for `j ≤ 7`**, extending
`Work.FTS.LocData6.Tfun_abs_le5` by two orders. -/
theorem Tfun_abs_le7 (j : ℕ) (hj : j ≤ 7) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 10000000 := by
  have hα0 : 0 ≤ α := le_of_lt hα
  have hv : |Real.cos (2 * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  by_cases h5 : j ≤ 5
  · exact (Work.FTS.LocData6.Tfun_abs_le5 j h5 α hα hα1 θ).trans (by norm_num)
  · have h6 : 6 ≤ j := by omega
    interval_cases j
    · rw [Tfun_eq_Qp 6 α]
      exact (Qp6_eval_bound hα0 hα1 hv).trans (by norm_num)
    · rw [Tfun_eq_Qp 7 α]
      exact (Qp7_eval_bound hα0 hα1 hv).trans (by norm_num)

/-- The angular jet bound `|D_θ^i Γ| ≤ 10⁷·Γ` on `Iθ`, for `i ≤ 8`.  As in the lower-order
files, the statement is reduced through `Work.Spaces.dthU_iter_Gam_abs_bound` to the
coefficient bound `|Tfun (i-1) α| ≤ 10⁷` (`Tfun_abs_le7`). -/
theorem DthIter_Gam_abs_le8 (i : ℕ) (hi : i ≤ 8) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 10000000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    nlinarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 10000000 :=
      fun θ' _ => Tfun_abs_le7 (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 10000000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 10000000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 10000000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS_LocDatum3a
