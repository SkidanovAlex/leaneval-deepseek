import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.PolySubstFirst

namespace Work.WilG4c

/-- **Simultaneous substitution in a two-variable polynomial.**  For `e₀, e₁, b : MvPolynomial (Fin 2) ℕ`
there is `b' : MvPolynomial (Fin 2) ℕ` with
`eval ![D, r] b' = eval ![eval ![D, r] e₀, eval ![D, r] e₁] b` for all `D r : ℕ`.

This is the degree bookkeeping of the §5.3 assembly: the degrees produced by the `Ω`-calculus are
composed expressions (e.g. `eval ![D, D₁] b` where `D₁ = eval ![D, r] dc` is itself a polynomial in
`(D, r)`), while the final `b` of an `FLemP` conclusion must be a polynomial in the *outer*
variables `(D, r)` alone. -/
theorem PolySubstBoth (e₀ e₁ b : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] b'
        = MvPolynomial.eval ![MvPolynomial.eval ![D, r] e₀, MvPolynomial.eval ![D, r] e₁] b := by
  refine ⟨MvPolynomial.aeval ![e₀, e₁] b, fun D r => ?_⟩
  rw [eval_aeval_eq]
  have hfun : (fun i => MvPolynomial.eval ![D, r] (![e₀, e₁] i))
      = ![(MvPolynomial.eval ![D, r]) e₀, (MvPolynomial.eval ![D, r]) e₁] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

end Work.WilG4c
