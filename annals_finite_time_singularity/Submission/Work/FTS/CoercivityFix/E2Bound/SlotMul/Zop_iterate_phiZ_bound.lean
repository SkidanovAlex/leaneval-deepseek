/-
Copyright: work module for the Elgindi finite-time singularity project.

# Uniform boundedness of the `Zop`-iterates of `φ(z) = z/(1+z)²` on `(0,∞)`

`Zop u = z ↦ z·u'(z)` (`Work.Spaces.Zop`).  We show that for every `n` there is a
constant `K ≥ 0` with `|Zop^[b] φ z| ≤ K` for all `b ≤ n` and all `z > 0`.

ROUTE.  Under the Möbius chart `w = zchart z = (z-1)/(z+1)` the profile is the
polynomial `φ = gpoly Pphi` with `Pphi = ¼(1 - X²)`, and `Zop` intertwines the chart
evaluation with the polynomial map `Tmul P = ½(1-X²)P'`:
`Zop (gpoly P) z = gpoly (Tmul P) z` for `z > 0` (proved in `Zop_gpoly_iterate`).
Iterating, `Zop^[b] φ z = gpoly (Tmul^[b] Pphi) z` for `z > 0`; since `z > 0` gives
`|zchart z| < 1`, each iterate is bounded by the sum of the absolute values of the
coefficients of `Tmul^[b] Pphi`, and there are only finitely many `b ≤ n`.

The two `Zop`-specific facts are taken from the sibling modules
`Zop_gpoly_iterate` and `Zop_iterate_eqOn_of_eqOn`; the elementary polynomial bound
from `Polynomial_abs_eval_le_sum_abs_coeff`.
-/
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

open Work.FTS.CoercivityFix.E2Bound (zchart gpoly Tmul Pphi)

set_option autoImplicit false

/-- Chart algebra: for `z ≠ -1`, `1 - zchart z ^ 2 = 4 z / (1 + z) ^ 2`. -/
lemma phiZ_one_sub_zchart_sq {z : ℝ} (hz : 1 + z ≠ 0) :
    1 - zchart z ^ 2 = 4 * z / (1 + z) ^ 2 := by
  have hz' : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  rw [zchart, div_pow]
  field_simp
  ring

/-- `gpoly Pphi` is the profile `φ z = z / (1 + z) ^ 2` (away from the pole `z = -1`). -/
lemma phiZ_gpoly_eq {z : ℝ} (hz : 1 + z ≠ 0) : gpoly Pphi z = z / (1 + z) ^ 2 := by
  rw [gpoly_apply, Pphi_eq]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [phiZ_one_sub_zchart_sq hz]
  ring

/-- For each `n` there is a common bound for the first `n` `Zop`-iterates of the profile
`φ(z) = z/(1+z)²` on the positive half-line. -/
theorem Zop_iterate_phiZ_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K := by
  refine ⟨∑ b ∈ Finset.range (n + 1),
    ∑ k ∈ Finset.range ((Tmul^[b] Pphi).natDegree + 1), |(Tmul^[b] Pphi).coeff k|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  · intro b hb z hz
    have hmem : b ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    -- transport the profile `φ` to the chart polynomial `gpoly Pphi`
    have hbase : Set.EqOn (fun y : ℝ => y / (1 + y) ^ 2) (gpoly Pphi) (Set.Ioi (0 : ℝ)) := by
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      have hy1 : 1 + y ≠ 0 := by intro h; linarith
      exact (phiZ_gpoly_eq hy1).symm
    have h1 : (Work.Spaces.Zop^[b] (fun y : ℝ => y / (1 + y) ^ 2)) z
        = gpoly (Tmul^[b] Pphi) z := by
      rw [Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hbase hz,
        Zop_gpoly_iterate Pphi b z hz]
    rw [h1]
    -- the chart variable lies in `(-1,1)`, so the polynomial evaluation is bounded by the
    -- sum of the absolute values of the coefficients
    have h2 : |gpoly (Tmul^[b] Pphi) z| ≤
        ∑ k ∈ Finset.range ((Tmul^[b] Pphi).natDegree + 1), |(Tmul^[b] Pphi).coeff k| := by
      have := Polynomial_abs_eval_le_sum_abs_coeff (Tmul^[b] Pphi)
        (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz)
      simpa [Work.FTS.CoercivityFix.E2Bound.gpoly] using this
    -- one term of a sum of nonnegative terms
    have h3 : (∑ k ∈ Finset.range ((Tmul^[b] Pphi).natDegree + 1), |(Tmul^[b] Pphi).coeff k|)
        ≤ ∑ b' ∈ Finset.range (n + 1),
            ∑ k ∈ Finset.range ((Tmul^[b'] Pphi).natDegree + 1), |(Tmul^[b'] Pphi).coeff k| :=
      Finset.single_le_sum (f := fun b' =>
          ∑ k ∈ Finset.range ((Tmul^[b'] Pphi).natDegree + 1), |(Tmul^[b'] Pphi).coeff k|)
        (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) hmem
    linarith

end Work.FTS.CoercivityFix.E2Bound.SlotMul
