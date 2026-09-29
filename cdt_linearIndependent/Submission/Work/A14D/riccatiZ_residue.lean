import Mathlib
import Submission.Work.A14D.riccatiZ_helpers

namespace Work.A14D

open Polynomial

noncomputable section

/-- At a root `β` of `B`, the cleared Riccati equation forces `A.eval β = B.derivative.eval β`.

The argument uses the two "coefficient at a root" identities of `riccatiZ_helpers`:

* evaluating `Q2Z·(A'B − AB') + Q2Z·A² + Q1Z·AB + Q0Z·B²` at `β` gives
  `Q2Z(β)·A(β)·(A(β) − B'(β)) = 0`, so if `Q2Z(β) ≠ 0` (and `A(β) ≠ 0` by coprimality) then
  `A(β) = B'(β)`;
* if instead `Q2Z(β) = 0`, differentiating and using `Q2Z' = Q1Z` gives `Q1Z(β)·A(β)² = 0`, and
  `Q1Z(β) ≠ 0` at the roots `0, 1, 1/9` of `Q2Z`, so `A(β) = 0` — a contradiction with
  coprimality, since `B(β) = 0`.

Hence `Q2Z(β) ≠ 0` always, giving `A(β) = B'(β)`; coprimality then makes `B'(β) = A(β) ≠ 0`,
so the quotient is `1`. -/
theorem riccatiZ_residue (A B : Polynomial ℂ) (hB : B.Monic) (hcop : IsCoprime A B)
    (h : Work.A14D.Q2Z * (A.derivative * B - A * B.derivative) + Work.A14D.Q2Z * A ^ 2
          + Work.A14D.Q1Z * A * B + Work.A14D.Q0Z * B ^ 2 = 0)
    {β : ℂ} (hβ : β ∈ B.roots) : A.eval β / B.derivative.eval β = 1 := by
  have hBβ : B.eval β = 0 := by
    rw [Polynomial.mem_roots hB.ne_zero, Polynomial.IsRoot.def] at hβ
    exact hβ
  have hAβ : A.eval β ≠ 0 :=
    Commons.Algebra.Polynomial.ne_zero_of_eval_eq_zero_of_isCoprime hcop.symm hBβ
  -- Evaluation at `β` of the cleared identity.
  have heval := local_residue_eval Q2Z Q1Z Q0Z A B β hBβ h
  -- `Q2Z.eval β ≠ 0`: otherwise `A.eval β = 0`, contradicting coprimality.
  have hQne : Q2Z.eval β ≠ 0 := by
    intro hQ0
    have hderiv := local_residue_deriv Q2Z Q1Z Q0Z A B β hQ0 hBβ h
    rw [Q2Z_derivative] at hderiv
    have hQ1 : Q1Z.eval β ≠ 0 := by
      rw [← Q2Z_derivative]
      exact Q2Z_deriv_eval_ne_zero_of_root hQ0
    have hsquare : Q1Z.eval β * A.eval β ^ 2 = 0 := by linear_combination hderiv
    have hA2 : A.eval β ^ 2 = 0 := (mul_eq_zero.mp hsquare).resolve_left hQ1
    exact hAβ (sq_eq_zero_iff.mp hA2)
  have hAeq : A.eval β = B.derivative.eval β := by
    have hsub : A.eval β - B.derivative.eval β = 0 := by
      rcases mul_eq_zero.mp heval with h1 | h1
      · exact absurd h1 (mul_ne_zero hQne hAβ)
      · exact h1
    exact sub_eq_zero.mp hsub
  have hB'ne : B.derivative.eval β ≠ 0 := by rw [← hAeq]; exact hAβ
  rw [hAeq]
  exact div_self hB'ne

end

end Work.A14D
