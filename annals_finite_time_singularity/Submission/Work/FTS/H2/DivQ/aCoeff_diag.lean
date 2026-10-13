import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology

set_option autoImplicit false

/-- **The diagonal coefficient.**  For every `i`, the top coefficient of the expansion of
`G^i (2κ ∂_x f)` is `a i i = (2κ)^{i+1}`.  This is the fact that makes the inversion of
`Submission/Work/FTS/H2/DivQ/NOTES.md` §4 work: `a i i` does not vanish on the near region
`[0,x₁]` (`κ ≥ 1/√2` there), so the top term of the expansion *dominates* the whole sum by the
pointwise Young inequality.

Proof: both `aCoeff` and `bCoeff` are instances of the general recursion `genCoeff` of
`Submission/Work/FTS/H2/DivQ/aCoeff_bounds.lean` (`aCoeff_eq_genCoeff` with initial datum `2κ`);
above the diagonal `genCoeff` vanishes (`genCoeff_zero`), so the recursion
`genCoeff_succ_succ` collapses at the diagonal to `genCoeff init (i+1) (i+1) = 2κ · genCoeff init i i`. -/
theorem aCoeff_diag (i : ℕ) : aCoeff i i = fun x => (2 * kappa x) ^ (i + 1) := by
  have key : ∀ i : ℕ, genCoeff (fun x : ℝ => 2 * kappa x) i i
      = fun x => (2 * kappa x) ^ (i + 1) := by
    intro i
    induction i with
    | zero =>
        rw [genCoeff_init_zero]
        funext x
        simp
    | succ i ih =>
        rw [genCoeff_succ_succ]
        have hzero : genCoeff (fun x : ℝ => 2 * kappa x) i (i + 1) = 0 :=
          genCoeff_zero _ i (i + 1) (Nat.lt_succ_self i)
        rw [hzero, ih]
        funext x
        have hd0 : deriv (0 : ℝ → ℝ) x = 0 := by
          simpa using (hasDerivAt_const (x := x) (c := (0 : ℝ))).deriv
        simp only [Pi.zero_apply, hd0, mul_zero, zero_mul, add_zero, zero_add, pow_succ]
        ring
  rw [show aCoeff i i = genCoeff (fun x : ℝ => 2 * kappa x) i i from aCoeff_eq_genCoeff i i]
  exact key i

end Work.FTS.H2.DivQ
