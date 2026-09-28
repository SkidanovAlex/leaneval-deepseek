import Mathlib
import Submission.Work.HP.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

/-- Directional derivative in the direction `b`, as a `ℚ`-linear map on polynomials. -/
def Db (b : Fin 5 → ℚ) : MvPolynomial (Fin 5) ℚ →ₗ[ℚ] MvPolynomial (Fin 5) ℚ :=
  ∑ i : Fin 5, b i • (pderiv i).toLinearMap

theorem Db_apply (b : Fin 5 → ℚ) (f : MvPolynomial (Fin 5) ℚ) :
    Db b f = ∑ i : Fin 5, b i • pderiv i f := by
  simp [Db]

/-- The `i`-th linear form of the parametrisation `p ↦ Σ_a p_a • w a`. -/
def linForm (w : Fin 3 → Fin 5 → ℚ) (i : Fin 5) : MvPolynomial (Fin 3) ℚ :=
  ∑ a : Fin 3, C (w a i) * X a

theorem eval_linForm (w : Fin 3 → Fin 5 → ℚ) (i : Fin 5) (p : Fin 3 → ℚ) :
    MvPolynomial.eval p (linForm w i) = ∑ a : Fin 3, p a * w a i := by
  simp only [linForm, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Substitution `x_i ↦ Σ_a p_a w_{a,i} + u_0 b_{1,i} + u_1 b_{2,i}`. -/
def sigma (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) :
    MvPolynomial (Fin 5) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ) :=
  aeval fun i => (C (linForm w i) + X (0 : Fin 2) * C (C (b₁ i))
    + X (1 : Fin 2) * C (C (b₂ i)) : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))

/-- The point at which `f` is evaluated to get `sigma w b₁ b₂ f`. -/
def substPoint (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (p : Fin 3 → ℚ) (u : Fin 2 → ℚ) :
    Fin 5 → ℚ :=
  fun i => (∑ a : Fin 3, p a * w a i) + u 0 * b₁ i + u 1 * b₂ i

/-- The `α`-th level form: the coefficient of `u^α` in `sigma w b₁ b₂ f`. -/
def levelForm (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (f : MvPolynomial (Fin 5) ℚ)
    (α : Fin 2 → ℕ) : MvPolynomial (Fin 3) ℚ :=
  (sigma w b₁ b₂ f).coeff (Finsupp.equivFunOnFinite.symm α)

theorem levelForm_def (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (α : Fin 2 → ℕ) :
    levelForm w b₁ b₂ f α
      = (sigma w b₁ b₂ f).coeff (Finsupp.equivFunOnFinite.symm α) := rfl

end Work.Q44Geom
