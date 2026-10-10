import Mathlib
import Submission.Work.MotC2.Negation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

variable {L : Type*} [Field L]

/-! ## Auxiliary computations for the quadratic resolvent of a Weierstrass curve

`D = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)` is the (quadratic) resolvent whose roots are the
`x`-coordinates of the points of order `2` on `E`.  The lemmas below compute `D.eval α` and
`D.derivative.eval α` in terms of the coefficients `aᵢ` of `E`. -/

/-- The derivative of `linCoef E = a₁X + a₃`. -/
lemma neTwo_linCoef_derivative (E : WeierstrassCurve L) :
    (linCoef E).derivative = Polynomial.C E.a₁ := by
  simp [linCoef]

/-- The derivative of `cubCoef E = X³ + a₂X² + a₄X + a₆`. -/
lemma neTwo_cubCoef_derivative (E : WeierstrassCurve L) :
    (cubCoef E).derivative =
      Polynomial.C ((3 : ℕ) : L) * Polynomial.X ^ 2 +
        Polynomial.C (E.a₂ * ((2 : ℕ) : L)) * Polynomial.X + Polynomial.C E.a₄ := by
  rw [cubCoef, Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.derivative_add,
    Polynomial.derivative_X_pow, Polynomial.derivative_C_mul_X_pow,
    Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.derivative_C]
  norm_num

/-- Evaluation of `linCoef E`. -/
lemma neTwo_linCoef_eval (E : WeierstrassCurve L) (α : L) :
    (linCoef E).eval α = E.a₁ * α + E.a₃ := by
  simp [linCoef]

/-- Evaluation of `cubCoef E`. -/
lemma neTwo_cubCoef_eval (E : WeierstrassCurve L) (α : L) :
    (cubCoef E).eval α = α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆ := by
  simp [cubCoef]

/-- The derivative of the resolvent `D = linCoef E ^ 2 + 4 * cubCoef E`, expanded. -/
lemma neTwo_D_derivative (E : WeierstrassCurve L) :
    (linCoef E ^ 2 + 4 * cubCoef E).derivative =
      Polynomial.C ((2 : ℕ) : L) * linCoef E * Polynomial.C E.a₁ +
        (4 : L[X]) * (Polynomial.C ((3 : ℕ) : L) * Polynomial.X ^ 2 +
          Polynomial.C (E.a₂ * ((2 : ℕ) : L)) * Polynomial.X + Polynomial.C E.a₄) := by
  rw [Polynomial.derivative_add, Polynomial.derivative_sq, Polynomial.derivative_mul,
    neTwo_linCoef_derivative, neTwo_cubCoef_derivative]
  simp

/-- `D'(α) = 2(a₁α + a₃)a₁ + 4(3α² + 2a₂α + a₄)`. -/
lemma neTwo_D_derivative_eval (E : WeierstrassCurve L) (α : L) :
    (linCoef E ^ 2 + 4 * cubCoef E).derivative.eval α =
      2 * (E.a₁ * α + E.a₃) * E.a₁ + 4 * (3 * α ^ 2 + 2 * E.a₂ * α + E.a₄) := by
  rw [neTwo_D_derivative]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, neTwo_linCoef_eval,
    Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_X]
  first | refl_ring1 | ring

/-- `D(α) = (a₁α + a₃)² + 4(α³ + a₂α² + a₄α + a₆)`. -/
lemma neTwo_sq_add_four_eval (E : WeierstrassCurve L) (α : L) :
    (linCoef E ^ 2 + 4 * cubCoef E).eval α =
      (E.a₁ * α + E.a₃) ^ 2 + 4 * (α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆) := by
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, neTwo_linCoef_eval,
    neTwo_cubCoef_eval]
  simp only [Polynomial.eval_ofNat]

/-- `D = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)` has no double root when `E` is elliptic and
`2 ≠ 0`.  Proof route: given `D.eval α = 0` and `D.derivative.eval α = 0`, set `β = -(a₁α + a₃)/2`;
then `Equation E α β` holds (`β² + (a₁α+a₃)β = -(a₁α+a₃)²/4 = c(α)`) and both partial derivatives
`W_Y = 2β + a₁α + a₃` and `W_X = a₁β - (3α² + 2a₂α + a₄)` vanish (`D'(α) = 2(a₁α+a₃)a₁ + 4c'(α) = 0`
gives `a₁β = 3α² + 2a₂α + a₄`).  This contradicts
`WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero` (`E.IsElliptic` gives `E.Δ ≠ 0` via
`W.coe_Δ' ▸ W.Δ'.ne_zero`).  Uses `Work.MotC2.linCoef`/`Work.MotC2.cubCoef` from
`Submission.Work.MotC2.Negation`. -/
lemma NeTwoNoDoubleRoot (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) ≠ 0) (α : L) :
    ¬ ((Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E).eval α = 0 ∧
      (Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E).derivative.eval α = 0) := by
  rintro ⟨h0, h1⟩
  rw [neTwo_sq_add_four_eval] at h0
  rw [neTwo_D_derivative_eval] at h1
  -- the candidate point `(α, β)`, `β = -(a₁α + a₃)/2`
  set β : L := -(E.a₁ * α + E.a₃) / 2 with hβdef
  have h4 : (4 : L) ≠ 0 := by
    have h : (2 : L) * 2 ≠ 0 := mul_ne_zero h2 h2
    rw [show (4 : L) = 2 * 2 by norm_num]
    exact h
  have hβ : 2 * β + (E.a₁ * α + E.a₃) = 0 := by
    rw [hβdef]; field_simp; ring
  -- `(α, β)` lies on the curve
  have hEq' : β ^ 2 + (E.a₁ * α + E.a₃) * β -
      (α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆) = 0 := by
    have key : 4 * (β ^ 2 + (E.a₁ * α + E.a₃) * β -
        (α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆)) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) (2 * β + (E.a₁ * α + E.a₃)) * hβ - h0
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h h4
    · exact h
  have hEq : WeierstrassCurve.Affine.Equation E α β := by
    rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial]
    linear_combination (norm := first | refl_ring1 | ring1) hEq'
  -- the two partial derivatives vanish
  have hWX : Polynomial.evalEval α β (WeierstrassCurve.Affine.polynomialX E) = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialX]
    have key : 4 * (E.a₁ * β - (3 * α ^ 2 + 2 * E.a₂ * α + E.a₄)) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) (2 * E.a₁) * hβ - h1
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h h4
    · exact h
  have hWY : Polynomial.evalEval α β (WeierstrassCurve.Affine.polynomialY E) = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialY]
    linear_combination (norm := first | refl_ring1 | ring1) hβ
  -- contradict nonsingularity of the (elliptic) curve
  have hΔ : E.Δ ≠ 0 := by
    rw [← WeierstrassCurve.coe_Δ' E]
    exact (E.Δ').ne_zero
  have hns : WeierstrassCurve.Affine.Nonsingular E α β :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq
  rcases hns.2 with h | h
  · exact h hWX
  · exact h hWY

end Work.MotC2
