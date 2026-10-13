import Submission.Work.Wilkies.Defs

namespace Work.WilkiesD.Poly

open WilkiesDesign WilkiesConjecture

/-- Substituting a constant for the first of three variables of a real polynomial produces a
polynomial in the remaining two variables: for every `D : ℕ` and `p : MvPolynomial (Fin 3) ℝ`
there is `f : MvPolynomial (Fin 2) ℝ` with `f.eval ![x, y] = p.eval ![D, x, y]` for all reals
`x, y`.  This turns the three-parameter count `poly(D, g, log H)` of `CountBound` (with `D`
fixed by the truncation step) into the two-parameter polynomial of the challenge statement. -/
theorem eval_subst_first_const (D : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ x y : ℝ, f.eval ![x, y] = p.eval ![(D : ℝ), x, y] := by
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C
    ![(MvPolynomial.C (D : ℝ)), MvPolynomial.X 0, MvPolynomial.X 1] p, fun x y => ?_⟩
  have hfun : (⇑(MvPolynomial.eval ![x, y]) ∘
      ![(MvPolynomial.C (D : ℝ)), MvPolynomial.X 0, MvPolynomial.X 1] : Fin 3 → ℝ)
      = ![(D : ℝ), x, y] := by
    funext i; fin_cases i <;> simp
  rw [← MvPolynomial.eval_assoc, hfun]

end Work.WilkiesD.Poly
