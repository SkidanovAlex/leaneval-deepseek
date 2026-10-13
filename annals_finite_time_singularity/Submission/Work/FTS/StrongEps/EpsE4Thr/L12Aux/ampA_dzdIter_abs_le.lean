import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

/-! ## The chart-side remainders `R_b`

Abbreviate `Tmul P = ½(1 - X²)·P'` and `Pphi = ¼(1 - X²)` (the chart-side pictures of
`Zop = z∂_z` and of `φ(z) = z/(1+z)²`, `E2Bound/ZopPhiDefs.lean`).  Since

  `Tmul ((1 - X²)·R) = ½(1 - X²)·((1 - X²)·R' - 2X·R) = (1 - X²)·(½((1 - X²)·R' - 2X·R))`,

the factor `(1 - X²)` is preserved by the iteration, and `Tmul^[b] Pphi = (1 - X²)·Rseq b`
with the recursion below. -/

/-- The chart-side remainder polynomials `R_b` of the iterates of `Pphi`: defined by
`Tmul^[b] Pphi = (1 - X²)·Rseq b`. -/
noncomputable def Rseq : ℕ → Polynomial ℝ
  | 0 => Polynomial.C (1 / 4)
  | k + 1 => Polynomial.C (1 / 2) *
      ((1 - Polynomial.X ^ 2) * Polynomial.derivative (Rseq k)
        - Polynomial.C 2 * Polynomial.X * Rseq k)

@[simp] lemma Rseq_zero : Rseq 0 = Polynomial.C (1 / 4) := rfl

@[simp] lemma Rseq_succ (k : ℕ) : Rseq (k + 1) = Polynomial.C (1 / 2) *
      ((1 - Polynomial.X ^ 2) * Polynomial.derivative (Rseq k)
        - Polynomial.C 2 * Polynomial.X * Rseq k) := rfl

/-- **The factor `(1 - X²)` is preserved by the `Tmul`-iteration**: `Tmul^[b] Pphi` is
`(1 - X²)` times the polynomial `Rseq b`. -/
lemma Tmul_iter_Pphi (b : ℕ) :
    Work.FTS.CoercivityFix.E2Bound.Tmul^[b] Work.FTS.CoercivityFix.E2Bound.Pphi
      = (1 - Polynomial.X ^ 2) * Rseq b := by
  induction b with
  | zero =>
      show Work.FTS.CoercivityFix.E2Bound.Pphi = (1 - Polynomial.X ^ 2) * Rseq 0
      rw [Work.FTS.CoercivityFix.E2Bound.Pphi_eq, Rseq_zero]
      ring
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Work.FTS.CoercivityFix.E2Bound.Tmul_apply,
        Rseq_succ]
      rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
        Polynomial.derivative_X_pow]
      norm_num
      ring

/-- Evaluating `(1 - X²)·R` in the chart: `gpoly ((1 - X²)·R) z = (1 - y²)·R(y)`, `y = zchart z`. -/
lemma gpoly_one_sub_sq_mul (R : Polynomial ℝ) (z : ℝ) :
    Work.FTS.CoercivityFix.E2Bound.gpoly ((1 - Polynomial.X ^ 2) * R) z
      = (1 - (Work.FTS.CoercivityFix.E2Bound.zchart z) ^ 2)
        * R.eval (Work.FTS.CoercivityFix.E2Bound.zchart z) := by
  simp only [Work.FTS.CoercivityFix.E2Bound.gpoly, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]

/-- `1 - y² = 4·φ(z)` for the chart variable `y = zchart z = (z-1)/(z+1)` (`z ≠ -1`). -/
lemma one_sub_zchart_sq (z : ℝ) (hz : z ≠ -1) :
    1 - (Work.FTS.CoercivityFix.E2Bound.zchart z) ^ 2 = 4 * (z / (1 + z) ^ 2) := by
  have h := Work.FTS.CoercivityFix.E2Bound.gpoly_Pphi (z := z) hz
  simp only [Work.FTS.CoercivityFix.E2Bound.gpoly, Work.FTS.CoercivityFix.E2Bound.Pphi,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one] at h
  rw [← h]
  ring

/-- **The `D_z`-iterates of the transfer profile `ampA α z = 2z/(c(α)(1+z)²)` are dominated by
`z/(1+z)²`** — in particular they are `O(z)` at `z → 0⁺` and `O(1/z)` at `z → ∞`.  (The
existing `E2pkg.ampA_dzdIter_bound` gives only *boundedness* on `(0,∞)`, which is not enough
for the boundary traces of the nonlocal term `-Γ(θ)·ampA α z·L₁₂(x)(z)` of `𝓛_Γ^T`: those need
the `z`-decay at `0⁺`.)

Route: `ampA α = (2/c(α))·φ` with `φ(z) = z/(1+z)²` (`ampA_eq_const_mul_fA`,
`Zop_iter_const_mul`), and the `Zop`-iterates of `φ` keep the factor `φ`:

* `Zop^[b] φ = gpoly (Tmul^[b] Pphi)` (`E2Bound.Zop_gpoly` iterated), and
  `Tmul P = ½(1-X²)·P'`, `Pphi = ¼(1-X²)`, so by induction `Tmul^[b] Pphi = (1-X²)·R_b` for
  polynomials `R_b`;
* on `(0,∞)` the chart variable `y = zchart z = (z-1)/(z+1)` lies in `[-1,1]`
  (`abs_zchart_le_one`) and `¼(1-y²) = φ(z)` exactly, so
  `|Zop^[b] φ z| = φ(z)·|R_b(y)| ≤ (Σ|coeffs of R_b|)·φ(z)`. -/
theorem ampA_dzdIter_abs_le (α : ℝ) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ K * (z / (1 + z) ^ 2) := by
  refine ⟨|2 / Work.Spaces.c α| * 4 * (Rseq b).sum (fun _ a => |a|), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (abs_nonneg _) (by norm_num)) ?_
    rw [Polynomial.sum_def]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · intro z hz
    -- the `φ`-iterate is dominated by `4·φ·(Σ|coeffs of Rseq b|)`
    have hkey : ∀ w : ℝ, 0 < w →
        |Work.Spaces.Zop^[b] (fun w : ℝ => w / (1 + w) ^ 2) w|
          ≤ 4 * (w / (1 + w) ^ 2) * (Rseq b).sum (fun _ a => |a|) := by
      intro w hw
      have hwm1 : w ≠ -1 := Work.FTS.CoercivityFix.E2Bound.zchart_ne_neg_one hw
      rw [Work.FTS.CoercivityFix.E2Bound.Zop_iter_gpoly b w hw, Tmul_iter_Pphi,
        gpoly_one_sub_sq_mul]
      rw [abs_mul, abs_of_nonneg (by rw [one_sub_zchart_sq w hwm1]; positivity)]
      rw [one_sub_zchart_sq w hwm1]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.CoercivityFix.E2Bound.poly_eval_abs_le _
          (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hw)) (by positivity)
    calc |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        = |(2 / Work.Spaces.c α) * Work.Spaces.Zop^[b] (fun w : ℝ => w / (1 + w) ^ 2) z| := by
            rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
              Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA,
              Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
      _ = |2 / Work.Spaces.c α| * |Work.Spaces.Zop^[b] (fun w : ℝ => w / (1 + w) ^ 2) z| :=
            abs_mul _ _
      _ ≤ |2 / Work.Spaces.c α| * (4 * (z / (1 + z) ^ 2) * (Rseq b).sum (fun _ a => |a|)) :=
            mul_le_mul_of_nonneg_left (hkey z hz) (abs_nonneg _)
      _ = (|2 / Work.Spaces.c α| * 4 * (Rseq b).sum (fun _ a => |a|)) * (z / (1 + z) ^ 2) := by
            ring

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
