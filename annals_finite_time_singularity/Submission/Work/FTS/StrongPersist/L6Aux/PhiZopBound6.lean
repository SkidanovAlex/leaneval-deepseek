/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `Zop`-iterates of `z ↦ 3/(1+z)` up to order six

`Work.Spaces.Zop u = (z ↦ z·u'(z))` is the one-dimensional radial derivation `D_z`.  We show
that the first seven `Zop`-iterates of the profile `Phi(z) = 3/(1+z)` are bounded on
`[0,∞)`, i.e. that the family `|Zop^[b] Phi|`, `b ≤ 6`, has a common bound `K > 0`.

ROUTE.  Under the Möbius chart `zchart z = (z-1)/(z+1)`, which maps `(0,∞)` into `(-1,1)`,
the function `z ↦ 3/(1+z)` is the chart evaluation `gpoly P3` of the linear polynomial
`P3 = (3/2)(1 - X)` (`gpoly P z = P.eval (zchart z)`), and `Zop` intertwines the chart
evaluation with the polynomial map `Tmul P = ½(1-X²)·P'`
(`Zop_iterate_eqOn_of_eqOn` transports the profile identity along `Ioi 0`, and
`Zop_gpoly_iterate` gives `Zop^[b] (gpoly P) = gpoly (Tmul^[b] P)` there).  Hence for `z > 0`

    `Zop^[b] Phi z = (Tmul^[b] P3).eval (zchart z)`,

whose absolute value is bounded by the sum of the absolute values of the coefficients of
`Tmul^[b] P3` because `|zchart z| < 1` on `(0,∞)`
(`Polynomial_abs_eval_le_sum_abs_coeff`).  There are only seven iterates to control, so the
sum of those coefficient sums is a uniform bound.  At the remaining point `z = 0` every
`Zop`-iterate of order `≥ 1` vanishes (`Zop u 0 = 0·(deriv u 0) = 0`) and order `0`
contributes `|Phi 0| = 3`, which the outer `max 3 ·` accounts for.
-/
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.FinalClock.PhiZopBound
import Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.StrongPersist.L6Aux

open Work.FTS.CoercivityFix.E2Bound (zchart gpoly Tmul)

/-- The linear chart polynomial `(3/2)(1 - X)`, whose chart evaluation is `z ↦ 3/(1+z)`. -/
def P3 : Polynomial ℝ := Polynomial.C (3 / 2) * (1 - Polynomial.X)

/-- The sum of the absolute values of the coefficients of a real polynomial (all the
coefficients, not only the generic ones below the degree). -/
def coeffSum (P : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k|

lemma coeffSum_nonneg (P : Polynomial ℝ) : 0 ≤ coeffSum P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Evaluating a real polynomial at a point of `[-1,1]` is bounded by the sum of the
absolute values of its coefficients. -/
lemma abs_eval_le_coeffSum (P : Polynomial ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    |P.eval t| ≤ coeffSum P :=
  Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff P ht

/-- The chart evaluation of `P3` is the profile `3/(1+z)` on `(0,∞)`. -/
lemma gpoly_P3 {z : ℝ} (hz : 0 < z) : gpoly P3 z = 3 / (1 + z) := by
  have hz1 : z + 1 ≠ 0 := by positivity
  rw [Work.FTS.CoercivityFix.E2Bound.gpoly_apply]
  simp only [P3, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C, Work.FTS.CoercivityFix.E2Bound.zchart_apply]
  field_simp
  ring

/-- The profile `z ↦ 3/(1+z)` agrees with the chart evaluation of `P3` on all of `(0,∞)`,
which is what `Zop_iterate_eqOn_of_eqOn` needs to transport the `Zop`-iterates. -/
lemma eqOn_three_div_gpoly :
    Set.EqOn (fun z : ℝ => 3 / (1 + z)) (gpoly P3) (Set.Ioi 0) :=
  fun _ hz => (gpoly_P3 hz).symm

/-- Every `Zop`-iterate of order `≥ 1` vanishes at `z = 0`, since `Zop u = z ↦ z·u'(z)`. -/
lemma Zop_iterate_zero_of_pos (g : ℝ → ℝ) {b : ℕ} (hb : 1 ≤ b) :
    Work.Spaces.Zop^[b] g 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
  have h : Work.Spaces.Zop^[k + 1] g = Work.Spaces.Zop (Work.Spaces.Zop^[k] g) :=
    Function.iterate_succ_apply' Work.Spaces.Zop k g
  rw [h]
  simp [Work.Spaces.Zop]

/-- **The `Zop`-iterates of `z ↦ 3/(1+z)` up to order six are uniformly bounded.** -/
theorem PhiZopBound6 : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ 6, ∀ z : ℝ, 0 ≤ z →
    |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K := by
  refine ⟨max 3 (∑ b ∈ Finset.range 7, coeffSum (Tmul^[b] P3)) + 1, by positivity, ?_⟩
  intro b hb z hz
  have hb7 : b ∈ Finset.range 7 := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
  have hle : coeffSum (Tmul^[b] P3)
      ≤ ∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3) :=
    Finset.single_le_sum (f := fun b' => coeffSum (Tmul^[b'] P3))
      (fun i _ => coeffSum_nonneg _) hb7
  have hBig : ∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3)
      ≤ max 3 (∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3)) + 1 := by
    have := le_max_right (3 : ℝ) (∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3))
    linarith
  have h3 : (3 : ℝ) ≤ max 3 (∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3)) :=
    le_max_left 3 _
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: order `0` contributes `3`, orders `≥ 1` contribute `0`
    subst hz0
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0
      have h0 : |Work.Spaces.Zop^[0] (fun z : ℝ => 3 / (1 + z)) (0 : ℝ)| = 3 := by
        rw [Function.iterate_zero_apply]
        norm_num
      rw [h0]
      linarith
    · rw [Zop_iterate_zero_of_pos (fun z : ℝ => 3 / (1 + z)) hbpos, abs_zero]
      linarith
  · -- `z > 0`: chart the iterate and bound it by its coefficient sum
    have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
        = (Tmul^[b] P3).eval (zchart z) := by
      rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi
            eqOn_three_div_gpoly hzpos,
          Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate P3 b z hzpos]
      rfl
    rw [h1]
    have h2 : |(Tmul^[b] P3).eval (zchart z)| ≤ coeffSum (Tmul^[b] P3) :=
      abs_eval_le_coeffSum _ (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hzpos)
    linarith

end Work.FTS.StrongPersist.L6Aux
