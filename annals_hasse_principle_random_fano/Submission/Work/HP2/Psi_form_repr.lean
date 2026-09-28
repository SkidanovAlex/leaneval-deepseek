import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP2.MvPoly_sum_mon
import Submission.Work.HP2.PsiPoly_homog

/-!
# `Ψ` as a form of degree `2d` in the Veronese coordinates

For a coefficient vector `a : Mon d n → ℤ` and a parameter `α : ℝ`, the cone condition
`a ∈ 𝒞_{ν(x)}^{(α)}` is equivalent to `Ψ d n a α x ≤ 0`, where

`Ψ d n a α x = 4α² (formEvalR d n (toR a) x)² − ‖a‖² ‖ν(x)‖²`.

The two terms are homogeneous of degree `2d` in `x`, so `Ψ` is a *form* of degree `2d`; written in
the monomial basis `veronese (2*d) n x η = ∏ i, x i ^ (η.1 i)` it therefore has a coefficient
vector `H : Mon (2*d) n → ℝ`.  That is the content of `Psi_form_repr` below:

`Ψ d n a α x = ∑ η, H η * veronese (2*d) n x η` for every `x`.

The proof realises `Ψ` as the evaluation of an explicit multivariate polynomial

`P = C (4α²) * (∑ m, C (a m) * ∏ i, X i ^ (m.1 i))² − C (‖a‖²) * (∑ m, (∏ i, X i ^ (m.1 i))²)`

(which is homogeneous of degree `2d` by `Work.HP2.PsiPoly_homog`, and whose evaluation is `Ψ` by
`eval_PsiPoly`), and takes `H η = P.coeff (Mon.toFinsupp η)`.  That this coefficient vector
reproduces the evaluation is exactly `Work.HP2.MvPoly_sum_mon`, the general statement that a
homogeneous polynomial of degree `2d` evaluates as the sum of its monomials grouped by exponent
vector.
-/

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset

namespace Work.HP2

open Work.HP

/-- Evaluation of a Veronese monomial: `eval x (∏ i, X i ^ (m.1 i)) = veronese d n x m`. -/
theorem eval_mon_prod (d n : ℕ) (x : Fin (n + 1) → ℝ) (m : Mon d n) :
    MvPolynomial.eval x (∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) = veronese d n x m := by
  rw [veronese, MvPolynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_X]

/-- Evaluating the polynomial form of `Ψ` at `x` returns `Ψ d n a α x`. -/
theorem eval_PsiPoly (d n : ℕ) (a : Mon d n → ℤ) (α : ℝ) (x : Fin (n + 1) → ℝ) :
    MvPolynomial.eval x
      (MvPolynomial.C (4 * α ^ 2) *
          (∑ m : Mon d n, MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2
        - MvPolynomial.C ((eNorm a) ^ 2) *
          (∑ m : Mon d n, (∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2))
      = Psi d n a α x := by
  have hA : MvPolynomial.eval x
        (∑ m : Mon d n, MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X i ^ (m.1 i : ℕ))
      = formEvalR d n (toR a) x := by
    rw [formEvalR, MvPolynomial.eval_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_mon_prod]
    rfl
  have hS : MvPolynomial.eval x
        (∑ m : Mon d n, (∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2)
      = (rNorm (veronese d n x)) ^ 2 := by
    rw [rNorm, Real.sq_sqrt (Finset.sum_nonneg fun m _ => sq_nonneg _), MvPolynomial.eval_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval_pow, eval_mon_prod]
  rw [Psi, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_C, MvPolynomial.eval_C, hA, hS]

/-- **`Ψ` is a form of degree `2d`**: it is a real linear combination of the degree-`2d` Veronese
monomials `veronese (2*d) n x η`. -/
theorem Psi_form_repr (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α : ℝ) :
    ∃ H : Work.HP.Mon (2 * d) n → ℝ, ∀ x : Fin (n + 1) → ℝ,
      Work.HP.Psi d n a α x
        = ∑ η : Work.HP.Mon (2 * d) n, H η * Work.HP.veronese (2 * d) n x η := by
  refine ⟨fun η => (MvPolynomial.C (4 * α ^ 2) *
        (∑ m : Mon d n, MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2
      - MvPolynomial.C ((eNorm a) ^ 2) *
        (∑ m : Mon d n, (∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2)).coeff (Mon.toFinsupp η), ?_⟩
  intro x
  rw [← eval_PsiPoly d n a α x, MvPoly_sum_mon d n _ (PsiPoly_homog d n a α) x]

end Work.HP2
