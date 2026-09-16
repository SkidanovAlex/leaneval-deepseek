import Submission.ZagierHoffmanProof.ATFormula

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the explicit Anderson–Thakur formula

Sanity checks of `atPsi_eq_atPsiClosed` against the independent definition of `Ψ_k`: the
degeneration `k = 0` (`Ψ_0(a) = a`), the interpolation property `Ψ_k(θ ^ k) = 1`, the
partial-fraction identities at `k = 1, 2`, and concrete instances over `ZMod 2` / `ZMod 3`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The definitional unfolding of the closed form. -/
lemma atPsiClosed_eq_sum (k : ℕ) (a : F[X]) :
    atPsiClosed F k a
      = ∑ j ∈ Finset.range (k + 1),
          (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ j)) a) * (atDen F k j)⁻¹ := rfl

/-- ★ Degeneration at `k = 0`: `Ψ_0(a) = a`. -/
lemma atPsiClosed_zero (a : F[X]) :
    atPsiClosed F 0 a = algebraMap F[X] (RatFunc F) a := by
  rw [← atPsi_eq_atPsiClosed, atPsi_zero_eq]

/-- ★ The interpolation property, transported to the closed form. -/
lemma atPsiClosed_X_pow_self (k : ℕ) :
    atPsiClosed F k (Polynomial.X ^ k) = 1 := by
  rw [← atPsi_eq_atPsiClosed]; exact atPsi_X_pow F k

/-- ★ The partial-fraction identity at `k = 1`: `1/L_1 + 1/D_1 = 0`. -/
lemma partialFraction_one : (atDen F 1 0)⁻¹ + (atDen F 1 1)⁻¹ = 0 := by
  have h := partialFraction F 1
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  simpa using h

/-- ★ The partial-fraction identity at `k = 2`. -/
lemma partialFraction_two : (atDen F 2 0)⁻¹ + (atDen F 2 1)⁻¹ + (atDen F 2 2)⁻¹ = 0 := by
  have h := partialFraction F 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
  simpa using h

/-- ★ The partial-fraction identity at `k = 3`. -/
lemma partialFraction_three :
    (atDen F 3 0)⁻¹ + (atDen F 3 1)⁻¹ + (atDen F 3 2)⁻¹ + (atDen F 3 3)⁻¹ = 0 := by
  have h := partialFraction F 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at h
  simpa using h

end ZagierHoffmanPositiveChar

section Concrete

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

/-- A closed-form identity of real content: `∑_{j ≤ 3} θ / (D_j L_{3-j} ^ (q^j)) = 0`. -/
example : atPsiClosed (ZMod 2) 3 Polynomial.X = 0 := by
  rw [← atPsi_eq_atPsiClosed]
  exact atPsi_eq_zero_of_lt_degree (ZMod 2) 3 Polynomial.X (by
    rw [Polynomial.natDegree_X]; norm_num)

/-- The closed form interpolates `θ` at the top layer. -/
example : atPsiClosed (ZMod 3) 1 (Polynomial.X ^ 1) = 1 :=
  atPsiClosed_X_pow_self (ZMod 3) 1

/-- The `k = 0` degeneration. -/
example : atPsiClosed (ZMod 3) 0 Polynomial.X
    = algebraMap (ZMod 3)[X] (RatFunc (ZMod 3)) Polynomial.X :=
  atPsiClosed_zero (ZMod 3) Polynomial.X

/-- The partial-fraction identities over concrete fields. -/
example : (atDen (ZMod 2) 1 0)⁻¹ + (atDen (ZMod 2) 1 1)⁻¹ = 0 :=
  partialFraction_one (ZMod 2)

example : (atDen (ZMod 3) 2 0)⁻¹ + (atDen (ZMod 3) 2 1)⁻¹ + (atDen (ZMod 3) 2 2)⁻¹ = 0 :=
  partialFraction_two (ZMod 3)

example : (atDen (ZMod 2) 3 0)⁻¹ + (atDen (ZMod 2) 3 1)⁻¹ + (atDen (ZMod 2) 3 2)⁻¹
    + (atDen (ZMod 2) 3 3)⁻¹ = 0 :=
  partialFraction_three (ZMod 2)

end Concrete
