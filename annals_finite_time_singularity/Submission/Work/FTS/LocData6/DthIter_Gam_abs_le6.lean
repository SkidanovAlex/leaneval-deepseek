/-
# `|D_θ^i Γ| ≤ 100000 · Γ` on `Iθ`, for `i ≤ 6`

This extends `Work.FTS.LocDataExt.DthIter_Gam_abs_le5` (the case `i ≤ 5`) by one order, to
the order required by the order-`6` data of this chapter (`LocData6`, see `NOTES.md` §1).

As in the two lower-order files, the statement is reduced through
`Work.Spaces.dthU_iter_Gam_abs_bound` to the coefficient bound `|Tfun j α θ| ≤ 100000` for
`j ≤ i - 1 ≤ 5`.  Recall `Tfun j α θ = (Qp j α).eval (cos 2θ)`, where the coefficient
polynomials obey

`Qp 0 α = X - 1/3`,   `Qp (j+1) α = -2(1-X²)·(Qp j α)' + α·(X-1/3)·(Qp j α)`.

So for `i ≤ 6` it remains to bound `Tfun 5 α`, i.e. `Qp 5 α` on `[-1,1]`.  The chain of
derivative recursions used is

* `(Qp (j+1))'   = 4v·(Qp j)' - 2(1-v²)·(Qp j)'' + α·(Qp j) + α(v-1/3)·(Qp j)'`
  (`Work.FTS.LocDataExt.Qp_deriv_succ_eval`),
* `(Qp (j+1))''  = (4+2α)·(Qp j)' + 8v·(Qp j)'' - 2(1-v²)·(Qp j)''' + α(v-1/3)·(Qp j)''`
  (`Qp_deriv_deriv_succ_eval`, proved here),

and the previously established bounds
`|(Qp 2)'| ≤ 154/3`, `|(Qp 2)''| ≤ 96` (`LocDataExt`), `|(Qp 3)| ≤ 10300/81`,
`|(Qp 3)'| ≤ 13072/27` (`LocData`).  Since `(Qp 2)''' = (4+2α)(12+3α)` is explicit, one gets

`|(Qp 3)''| ≤ 6·(154/3) + 8·96 + 2·90 + (4/3)·96 = 1384`,
`|(Qp 4)'| ≤ 4·(13072/27) + 2·1384 + 10300/81 + (4/3)·(13072/27) = 443660/81`,
`|Qp 4| ≤ 2·(13072/27) + (4/3)·(10300/81) = 276496/243`,
`|Qp 5| ≤ 2·(443660/81) + (4/3)·(276496/243) = 9091864/729 ≤ 100000`.

Everything rests on `[propext, Classical.choice, Quot.sound]` only.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.DthIter_Gam_abs_le5
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.LocData

/-! ## The second derivative recursion for the coefficient polynomials `Qp` -/

/-- The second derivative recursion for the coefficient polynomials, obtained by
differentiating `(Q_{j+1})' = 4v·Q_j' - 2(1-v²)·Q_j'' + α·Q_j + α(v-1/3)·Q_j'`. -/
theorem Qp_deriv_deriv_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp j α).derivative.eval v
        + 8 * v * (Qp j α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp j α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.derivative.eval v := by
  simp [Qp]; ring

/-- `Qp 1 α` is a quadratic polynomial, so its third derivative vanishes. -/
theorem Qp1_deriv3_eval (α v : ℝ) :
    (Qp 1 α).derivative.derivative.derivative.eval v = 0 := by
  simp [Qp]

/-- The third derivative of `Qp 2 α`, explicitly. -/
theorem Qp2_deriv3_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.derivative.eval v = (4 + 2 * α) * (12 + 3 * α) := by
  simp [Qp]; ring

/-- **Bound on `(Qp 2 α)'''`** on `|v| ≤ 1`, `α ∈ [0,1]`. -/
theorem Qp2_deriv3_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 := by
  rw [Qp2_deriv3_eval, abs_mul]
  have h1 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have h2 : |12 + 3 * α| ≤ 15 := by rw [abs_le]; constructor <;> linarith
  calc |4 + 2 * α| * |12 + 3 * α| ≤ 6 * 15 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 90 := by norm_num

/-- The second derivative recursion at `j = 2`, i.e. for `Qp 3`. -/
theorem Qp3_deriv2_eval (α v : ℝ) :
    (Qp 3 α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp 2 α).derivative.eval v
        + 8 * v * (Qp 2 α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v :=
  Qp_deriv_deriv_succ_eval 2 α v

/-- **Bound on `(Qp 3 α)''`.**  With `|(Qp 2)'| ≤ 154/3`, `|(Qp 2)''| ≤ 96` and
`|(Qp 2)'''| ≤ 90`, the recursion gives `|(Qp 3)''| ≤ 6·(154/3) + 8·96 + 2·90 + (4/3)·96 = 1384`. -/
theorem Qp3_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 := by
  rw [Qp3_deriv2_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hS2 : |(Qp 2 α).derivative.eval v| ≤ 154 / 3 := Qp2_deriv_bound hα0 hα1 hv
  have hU2 : |(Qp 2 α).derivative.derivative.eval v| ≤ 96 :=
    Work.FTS.LocDataExt.Qp2_deriv2_bound hα0 hα1 hv
  have hT2 : |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 :=
    Qp2_deriv3_bound hα0 hα1
  have hA : |(4 + 2 * α) * (Qp 2 α).derivative.eval v| ≤ 6 * (154 / 3) :=
    abs_mul_le_of (A := 6) (B := 154 / 3) h4 hS2 (by norm_num)
  have hB : |8 * v * (Qp 2 α).derivative.derivative.eval v| ≤ 8 * 1 * 96 := by
    rw [show 8 * v * (Qp 2 α).derivative.derivative.eval v
        = (8 * v) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 8 * 1) (B := 96)
      (by rw [abs_mul]; norm_num; exact hv) hU2 (by norm_num)
  have hC : |(-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v|
      ≤ 2 * 1 * 90 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 90)
      (by rw [abs_mul]; norm_num; exact h1) hT2 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v| ≤ 1 * (4 / 3) * 96 := by
    rw [show α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 96)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hU2 (by norm_num)
  have hsp1 := abs_add_le ((4 + 2 * α) * (Qp 2 α).derivative.eval v
      + 8 * v * (Qp 2 α).derivative.derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v)
      (α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v)
  have hsp2 := abs_add_le ((4 + 2 * α) * (Qp 2 α).derivative.eval v
      + 8 * v * (Qp 2 α).derivative.derivative.eval v)
      ((-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v)
  have hsp3 := abs_add_le ((4 + 2 * α) * (Qp 2 α).derivative.eval v)
      (8 * v * (Qp 2 α).derivative.derivative.eval v)
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-! ## `Qp 4` -/

/-- The derivative recursion at `j = 3`, i.e. for `Qp 4`. -/
theorem Qp4_deriv_eval (α v : ℝ) :
    (Qp 4 α).derivative.eval v
      = 4 * v * (Qp 3 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v
        + α * (Qp 3 α).eval v
        + α * (v - 1 / 3) * (Qp 3 α).derivative.eval v :=
  Work.FTS.LocDataExt.Qp_deriv_succ_eval 3 α v

/-- **Bound on `(Qp 4 α)'`.**  From `|(Qp 3)| ≤ 10300/81`, `|(Qp 3)'| ≤ 13072/27` and
`|(Qp 3)''| ≤ 1384`: `4·(13072/27) + 2·1384 + 10300/81 + (4/3)·(13072/27) = 443660/81`. -/
theorem Qp4_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 := by
  rw [Qp4_deriv_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS3 : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 :=
    Work.FTS.LocDataExt.Qp3_deriv_bound hα0 hα1 hv
  have hU3 : |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 := Qp3_deriv2_bound hα0 hα1 hv
  have hQ3 : |(Qp 3 α).eval v| ≤ 10300 / 81 := Qp3_eval_bound hα0 hα1 hv
  have hA : |4 * v * (Qp 3 α).derivative.eval v| ≤ 4 * 1 * (13072 / 27) := by
    rw [show 4 * v * (Qp 3 α).derivative.eval v
        = (4 * v) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 * 1) (B := 13072 / 27)
      (by rw [abs_mul]; norm_num; exact hv) hS3 (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v| ≤ 2 * 1 * 1384 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 1384)
      (by rw [abs_mul]; norm_num; exact h1) hU3 (by norm_num)
  have hC : |α * (Qp 3 α).eval v| ≤ 1 * (10300 / 81) :=
    abs_mul_le_of (A := 1) (B := 10300 / 81) (by rwa [abs_of_nonneg hα0]) hQ3 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 3 α).derivative.eval v| ≤ 1 * (4 / 3) * (13072 / 27) := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 13072 / 27)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hS3 (by norm_num)
  have hsp1 := abs_add_le (4 * v * (Qp 3 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v
      + α * (Qp 3 α).eval v) (α * (v - 1 / 3) * (Qp 3 α).derivative.eval v)
  have hsp2 := abs_add_le (4 * v * (Qp 3 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v) (α * (Qp 3 α).eval v)
  have hsp3 := abs_add_le (4 * v * (Qp 3 α).derivative.eval v)
      ((-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v)
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-- **The sharp bound on `Qp 4 α`** (the `LocDataExt.Qp4_eval_bound` constant, made explicit). -/
theorem Qp4_eval_bound_sharp {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).eval v| ≤ 276496 / 243 := by
  rw [Work.FTS.LocDataExt.Qp4_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS3 : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 :=
    Work.FTS.LocDataExt.Qp3_deriv_bound hα0 hα1 hv
  have hQ3 : |(Qp 3 α).eval v| ≤ 10300 / 81 := Qp3_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v| ≤ 2 * 1 * (13072 / 27) := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 13072 / 27)
      (by rw [abs_mul]; norm_num; exact h1) hS3 (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 3 α).eval v| ≤ 1 * (4 / 3) * (10300 / 81) := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 10300 / 81)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ3 (by norm_num)
  calc |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v + α * (v - 1 / 3) * (Qp 3 α).eval v|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (13072 / 27) + 1 * (4 / 3) * (10300 / 81) := add_le_add hA hB
    _ = 276496 / 243 := by norm_num

/-! ## `Qp 5` -/

/-- The recursion at `j = 4`, i.e. for `Qp 5`. -/
theorem Qp5_eval (α v : ℝ) :
    (Qp 5 α).eval v
      = (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 4 α).eval v :=
  Qp_succ_eval 4 α v

/-- **Bound on `Qp 5 α` on `[-1,1]`.**  `|Qp 5| ≤ 2·(443660/81) + (4/3)·(276496/243)
= 9091864/729 < 10⁵`. -/
theorem Qp5_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 5 α).eval v| ≤ 100000 := by
  rw [Qp5_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hD4 : |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 := Qp4_deriv_bound hα0 hα1 hv
  have hQ4 : |(Qp 4 α).eval v| ≤ 276496 / 243 := Qp4_eval_bound_sharp hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v| ≤ 2 * 1 * (443660 / 81) := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 4 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 443660 / 81)
      (by rw [abs_mul]; norm_num; exact h1) hD4 (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 4 α).eval v| ≤ 1 * (4 / 3) * (276496 / 243) := by
    rw [show α * (v - 1 / 3) * (Qp 4 α).eval v
        = (α * (v - 1 / 3)) * (Qp 4 α).eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 276496 / 243)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ4 (by norm_num)
  calc |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 4 α).eval v|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (443660 / 81) + 1 * (4 / 3) * (276496 / 243) := add_le_add hA hB
    _ = 9091864 / 729 := by norm_num
    _ ≤ 100000 := by norm_num

/-! ## The coefficient bound for `j ≤ 5`, and the main statement -/

/-- **The coefficient bound `|Tfun j α θ| ≤ 100000` for `j ≤ 5`**, extending
`Work.FTS.LocDataExt.Tfun_abs_le4` by one order. -/
theorem Tfun_abs_le5 (j : ℕ) (hj : j ≤ 5) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 100000 := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact Work.FTS.LocDataExt.Tfun_abs_le4 j (by omega) α hα hα1 θ
  · subst heq
    have hq : |(Qp 5 α).eval (Real.cos (2 * θ))| ≤ 100000 :=
      Qp5_eval_bound (le_of_lt hα) hα1
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    rw [Tfun_eq_Qp 5 α]
    simpa using hq

/-- The angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` on `Iθ`, extended by one order (to `i ≤ 6`).
The proved `i ≤ 5` version `Work.FTS.LocDataExt.DthIter_Gam_abs_le5` reduces the statement to
a bound `|Tfun (i-1) α θ| ≤ 100000`, so it suffices to bound `Qp 5 α` on `|v| ≤ 1`,
`α ∈ [0,1]` through the recursion `Qp (j+1) = -2(1-X²)·Qp j' + α·(X-1/3)·Qp j` and its first two
derivatives, and then to re-run the final assembly of that file
(`Work.Spaces.dthU_iter_Gam_abs_bound`). -/
theorem DthIter_Gam_abs_le6 (i : ℕ) (hi : i ≤ 6) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 100000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    linarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Tfun_abs_le5 (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 100000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS.LocData6
