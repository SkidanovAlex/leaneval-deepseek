import Mathlib
import Submission.Work.C17y.adj_setup
import Submission.Work.C17y.adj_assembly
import Submission.Work.C17y.adj_core

/-!
# The adjoint equation `B'' − p₁B' + (p₀ − p₁')B = Σ cᵢ y^{i−4}y'` has only the trivial solution

`Work.C17y.adjoint_no_solution_rat`: for an admissible pair `(a,b)` (`Work.C17.AdmQ a b`) the
equation `LBE a b B = Σᵢ cᵢ·y^{i−4}·y'` (`y = x²/(x−1)`) with `B ∈ ℚ(x)`, `cᵢ ∈ ℚ` forces
`B = 0` and `c = 0`.

The proof is assembled in `Submission/Work/C17y/adj_assembly.lean`: the substitution
`β = B/P₂` turns the operator `LBE` into the formal adjoint `Lst` of the order-two operator `M`
of the CDT paper; the divisor bound `Work.C17adj.adjoint_divisor_boundC` (over `ℂ`, with the
descent `adj_divisor_descent` to `ℚ`) bounds every solution by `β·x⁶(x²−1)² = N`, `deg N ≤ 6`;
the denominator-cleared certificate (`Work.C17adj.adjoint_clearing`, `Work.C17adj.Gpoly_eq_Epoly`)
turns the equation into `Work.C17.Gpoly a b n c = 0`, and the linear-algebra certificate
`Work.C17.linear_core` (in `Submission/Work/C17/adjoint_core.lean`) forces `n = 0`, `c = 0`.
-/

namespace Work.C17y

theorem adjoint_no_solution_rat (a b : ℚ) (hA : Work.C17.AdmQ a b) (B : RatFunc ℚ) (c : Fin 6 → ℚ)
    (h : Work.C17y.LBE a b B = ∑ i : Fin 6, ((c i : ℚ) : RatFunc ℚ) * Work.C17y.rQ i) :
    B = 0 ∧ c = 0 :=
  adjoint_no_solution_rat_assembly
    (fun a b hA n c hG => Work.C17y.Core.linear_core a b hA n c hG) a b hA B c h

end Work.C17y
