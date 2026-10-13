import Mathlib
import Submission.Work.WilE7.poly_embed

namespace Work.WilE7.CoreStep

/-- Polynomial bookkeeping (bivariate, exact form): for any two polynomials `p B` over `ℕ` there is a bivariate polynomial `N` over `ℕ` whose value at `![D, k]` is *exactly* `k * p.eval D * B.eval (p.eval D)`.  This is the shape of the size bound of the family-level stratum list: `k` pieces per member of the `k`-family, each contributing `p.eval D` pieces, each of which contributes at most `B.eval (p.eval D)` strata.  A witness is `N := MvPolynomial.X 1 * Polynomial.aeval (MvPolynomial.X 0) (p * B.comp p)`, using `Work.WilE7.eval_aeval_X_zero` and `Polynomial.eval_comp`; the final goal is the associativity of `ℕ`-multiplication, `ring_nf` closes it. -/
theorem polyOuterN (p B : Polynomial ℕ) :
    ∃ N : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval ![D, k] N = k * p.eval D * B.eval (p.eval D) := by
  refine ⟨MvPolynomial.X (1 : Fin 2) *
      Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (p * B.comp p), fun D k => ?_⟩
  rw [map_mul, MvPolynomial.eval_X]
  have h := Work.WilE7.eval_aeval_X_zero (p * B.comp p) (![D, k] : Fin 2 → ℕ)
  rw [show (![D, k] : Fin 2 → ℕ) 0 = D from by simp] at h
  rw [h, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [show (![D, k] : Fin 2 → ℕ) 1 = k from by simp]
  ring

end Work.WilE7.CoreStep
