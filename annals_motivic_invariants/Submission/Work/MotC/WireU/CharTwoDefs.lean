import Mathlib
import Submission.Work.MotC.WireU.WeierstrassCharP
import Submission.Work.Genus.Order.ord_add_eq_of_lt
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.ord_div_rat
import Submission.Work.Genus.Order.ord_aeval_of_neg
import Submission.Work.Genus.Order.ord_aeval_nonneg
import Submission.Work.Genus.Order.ord_deriv_ge
import Submission.Work.Genus.Order.ord_deriv_nonneg
import Submission.Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_div
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Genus.OrderInf.ordInf_aeval_of_neg
import Submission.Work.Genus.OrderInf.ordInf_aeval_nonneg
import Submission.Work.Genus.OrderInf.ordInf_add_eq_of_lt
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add
import Submission.Work.Genus.OrderInf.ordInf_deriv_ge
import Submission.Work.Genus.OrderInf.two_le_ordInf_deriv
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.Deriv.deriv_weierstrass
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic
import Submission.Work.Genus.Main.exists_ord_neg_or_ordInf_neg
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.CharP.Defs
import Submission.Work.Genus.CharP.equation_rootTwist
import Submission.Work.Genus.CharP.rootTwist_discriminant
import Submission.Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero
import Submission.Work.Genus.CharP.natDegree_num_pow
import Submission.Work.Genus.CharP.natDegree_denom_pow
import Submission.Work.Genus.CharP.size_lt_of_pow_eq
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The character-two Weierstrass rigidity: the basic objects

This module collects the definitions and the elementary algebraic identities used by the proof
that a non-singular Weierstrass curve over a field `K` of characteristic two has no non-constant
`K(t)`-point (`Work.Wire123.exists_algebraMap_of_weierstrass_ratFunc_charTwo`).

The Weierstrass equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` is rewritten as
`y (y + W) = A(x)` with

* `wOf E x = W = a₁x + a₃`, the `y`-partial derivative `∂F/∂y`,
* `cubicA E = A = X³ + a₂X² + a₄X + a₆`,
* `etaOf E x y = η = a₁y + x² + a₄`, the `x`-partial derivative `∂F/∂x`,
* `phiPoly E = Φ = (X² + a₄)² + a₁²A(X)`, so that `Φ(x) = η² + a₁²W y`.

In characteristic two the two partial derivatives `η`, `W` have **no common zero** on the curve:
the residue `a₁⁴Φ(a₃/a₁) = Δ` is the discriminant (`a1_pow_four_phiPoly_eval_div_eq_delta`).
-/

namespace Work.MotC.WireU

open Polynomial

section CharTwoDefs

variable {K : Type*} [Field K] [CharP K 2]

/-- `Φ(T) = (T² + a₄)² + a₁² (T³ + a₂ T² + a₄ T + a₆)`. -/
noncomputable def phiPoly (E : WeierstrassCurve K) : Polynomial K :=
  (X ^ 2 + C E.a₄) ^ 2
    + (C E.a₁) ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)

/-- The cubic `A(T) = T³ + a₂ T² + a₄ T + a₆` of the Weierstrass equation. -/
noncomputable def cubicA (E : WeierstrassCurve K) : Polynomial K :=
  X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆

/-- `W = a₁ x + a₃`, the `y`-partial derivative of the Weierstrass equation. -/
noncomputable def wOf (E : WeierstrassCurve K) (x : RatFunc K) : RatFunc K :=
  algebraMap K (RatFunc K) E.a₁ * x + algebraMap K (RatFunc K) E.a₃

/-- `η = a₁ y + x² + a₄`, the `x`-partial derivative of the Weierstrass equation. -/
noncomputable def etaOf (E : WeierstrassCurve K) (x y : RatFunc K) : RatFunc K :=
  algebraMap K (RatFunc K) E.a₁ * y + x ^ 2 + algebraMap K (RatFunc K) E.a₄

@[simp]
theorem phiPoly_eq (E : WeierstrassCurve K) :
    phiPoly E = (X ^ 2 + C E.a₄) ^ 2
      + (C E.a₁) ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) := rfl

@[simp]
theorem cubicA_eq (E : WeierstrassCurve K) :
    cubicA E = X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆ := rfl

@[simp]
theorem wOf_eq (E : WeierstrassCurve K) (x : RatFunc K) :
    wOf E x = algebraMap K (RatFunc K) E.a₁ * x + algebraMap K (RatFunc K) E.a₃ := rfl

@[simp]
theorem etaOf_eq (E : WeierstrassCurve K) (x y : RatFunc K) :
    etaOf E x y = algebraMap K (RatFunc K) E.a₁ * y + x ^ 2
      + algebraMap K (RatFunc K) E.a₄ := rfl

theorem aeval_cubicA (E : WeierstrassCurve K) (x : RatFunc K) :
    aeval x (cubicA E) = x ^ 3 + algebraMap K (RatFunc K) E.a₂ * x ^ 2
      + algebraMap K (RatFunc K) E.a₄ * x + algebraMap K (RatFunc K) E.a₆ := by
  simp only [cubicA_eq, map_add, map_mul, map_pow, aeval_X, aeval_C]

theorem cubicA_natDegree (E : WeierstrassCurve K) : (cubicA E).natDegree = 3 := by
  rw [show cubicA E = C (1 : K) * X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆ from by
    simp [cubicA]]
  exact Polynomial.natDegree_cubic one_ne_zero

/-- The exponent of the leading term of `cubicA` is positive. -/
theorem cubicA_natDegree_pos (E : WeierstrassCurve K) : 0 < (cubicA E).natDegree := by
  rw [cubicA_natDegree]; norm_num

/-- **The residue computation.**  `a₁⁴ Φ(a₃/a₁) = Δ`. -/
theorem a1_pow_four_phiPoly_eval_div_eq_delta (E : WeierstrassCurve K) (ha1 : E.a₁ ≠ 0) :
    E.a₁ ^ 4 * (phiPoly E).eval (E.a₃ / E.a₁) = E.Δ := by
  rw [WeierstrassCurve.Δ_of_char_two, WeierstrassCurve.b₈_of_char_two, phiPoly]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (norm := first | refl_ring1 | ring1) (E.a₃ ^ 2 * E.a₁ ^ 2 * E.a₄) * h2

/-- `a₁ ≠ 0 ∨ a₃ ≠ 0` for a curve of non-zero discriminant in characteristic two. -/
theorem a1_ne_zero_or_a3_ne_zero (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0) :
    E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h3⟩ := h
  exact hΔ (by rw [WeierstrassCurve.Δ_of_char_two, h1, h3]; ring)

/-- **The Weierstrass equation, rewritten.**  `y² = A(x) + W y`. -/
theorem y_sq_eq (E : WeierstrassCurve K) {x y : RatFunc K} (h : Work.Genus.CharP.WEqn E x y) :
    y ^ 2 = aeval x (cubicA E) + wOf E x * y := by
  have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
  have hc : aeval x (cubicA E) = x ^ 3 + algebraMap K (RatFunc K) E.a₂ * x ^ 2
      + algebraMap K (RatFunc K) E.a₄ * x + algebraMap K (RatFunc K) E.a₆ := aeval_cubicA E x
  rw [hc]
  unfold wOf
  unfold Work.Genus.CharP.WEqn at h
  linear_combination (norm := first | refl_ring1 | ring1) h - (algebraMap K (RatFunc K) E.a₁ * x * y + algebraMap K (RatFunc K) E.a₃ * y) * h2

/-- **Completing the square, in characteristic two.**  `Φ(x) = η² + a₁² W y`. -/
theorem aeval_phiPoly_eq (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) :
    aeval x (phiPoly E)
      = etaOf E x y ^ 2 + algebraMap K (RatFunc K) (E.a₁ ^ 2) * wOf E x * y := by
  have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
  unfold phiPoly etaOf wOf
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
  unfold Work.Genus.CharP.WEqn at h
  linear_combination (norm := first | refl_ring1 | ring1) (-(algebraMap K (RatFunc K) E.a₁ ^ 2)) * h
    + (-(algebraMap K (RatFunc K) E.a₁ * y * (x ^ 2 + algebraMap K (RatFunc K) E.a₄))) * h2

/-- **The differentiated Weierstrass equation in characteristic two.**  `W · y' = η · x'`. -/
theorem deriv_identity (E : WeierstrassCurve K) {x y : RatFunc K}
    (h : Work.Genus.CharP.WEqn E x y) :
    wOf E x * Work.Genus.deriv y = etaOf E x y * Work.Genus.deriv x := by
  have h2 : (2 : RatFunc K) = 0 := CharP.cast_eq_zero _ _
  have hdw := Work.Genus.Deriv.deriv_weierstrass E h
  unfold wOf etaOf at *
  linear_combination (norm := first | refl_ring1 | ring1) hdw + (- y * Work.Genus.deriv y
      + (x ^ 2 + algebraMap K (RatFunc K) E.a₂ * x - algebraMap K (RatFunc K) E.a₁ * y)
        * Work.Genus.deriv x) * h2

/-- The order at a finite place of a non-zero constant of `K(t)` is zero. -/
theorem ord_algebraMap_eq_zero (π : Polynomial K) (c : K) :
    Work.Genus.ord π (algebraMap K (RatFunc K) c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Work.Genus.Order.ord_zero]
  · rw [← mul_one (algebraMap K (RatFunc K) c), Work.Genus.Order.ord_C_mul hc,
      Work.Genus.Order.ord_one]

/-- The order at infinity of a non-zero constant of `K(t)` is zero. -/
theorem ordInf_algebraMap_eq_zero (c : K) : Work.Genus.ordInf (algebraMap K (RatFunc K) c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Work.Genus.ordInf, RatFunc.intDegree_zero]
  · rw [← mul_one (algebraMap K (RatFunc K) c), Work.Genus.OrderInf.ordInf_C_mul hc]
    simp [Work.Genus.ordInf, RatFunc.intDegree]

/-- The constant `algebraMap K (RatFunc K) c` is non-zero exactly when `c` is. -/
theorem algebraMap_ratFunc_ne_zero_iff {c : K} :
    algebraMap K (RatFunc K) c ≠ 0 ↔ c ≠ 0 := by
  constructor
  · intro h hc; exact h (by rw [hc, map_zero])
  · intro h hc
    rw [RatFunc.algebraMap_eq_C] at hc
    exact h (RatFunc.C_injective (by rw [hc, map_zero]))

end CharTwoDefs

end Work.MotC.WireU
