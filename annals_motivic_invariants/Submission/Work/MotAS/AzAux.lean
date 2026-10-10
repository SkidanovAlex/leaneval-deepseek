import Mathlib
import Submission.Work.MotAS.AzDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary lemmas for `Work.MotAS.azPrimeFwVec0`

Three small inputs of the final assembly of `Submission/Work/MotAS/azPrimeFwVec0.lean`:

* `azA_algebraMap`, `azB_algebraMap` : the scalars `A = azA a b`, `B = azB a b` commute with the
  push `𝕜 → RatFunc 𝕜`;
* `azC2_ne_zero` : the leading coefficient of the quadratic `azQ` is nonzero as soon as `A ≠ 0`:
  it factors as `4A·(A·X₂² + B)`, the second factor being nonzero because its `X₂²`-coefficient is
  `A ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-- `azA` of the pushed parameters is the push of `a² − ab − b²`. -/
theorem azA_algebraMap (𝕜 : Type) [Field 𝕜] (a b : 𝕜) :
    azA (algebraMap 𝕜 (RatFunc 𝕜) a) (algebraMap 𝕜 (RatFunc 𝕜) b)
      = algebraMap 𝕜 (RatFunc 𝕜) (a ^ 2 - a * b - b ^ 2) := by
  simp only [azA, map_sub, map_mul, map_pow]

/-- `azB` of the pushed parameters is the push of `a² + b²`. -/
theorem azB_algebraMap (𝕜 : Type) [Field 𝕜] (a b : 𝕜) :
    azB (algebraMap 𝕜 (RatFunc 𝕜) a) (algebraMap 𝕜 (RatFunc 𝕜) b)
      = algebraMap 𝕜 (RatFunc 𝕜) (a ^ 2 + b ^ 2) := by
  simp only [azB, map_add, map_pow]

/-- **The leading coefficient `azC2` is nonzero** as soon as `A ≠ 0` (in characteristic `5`): it
factors as `4A·(A·X₂² + B)` with `4A ≠ 0`, and `A·X₂² + B ≠ 0` because its coefficient at the
monomial `X₂²` is `A ≠ 0`. -/
theorem azC2_ne_zero (a b : K) [CharP K 5] (hA : azA a b ≠ 0) : azC2 a b ≠ 0 := by
  have h4 : (4 : K) ≠ 0 := by
    intro h
    have h54 : (5 : ℕ) ∣ 4 := (CharP.cast_eq_zero_iff K 5 4).mp h
    norm_num at h54
  have hfac : azC2 a b
      = C (4 * azA a b) * (C (azA a b) * X 1 ^ 2 + C (azB a b)) := by
    simp only [azC2]
    simp only [map_mul, map_pow, map_ofNat]
    first | refl_ring1 | ring
  rw [hfac]
  refine mul_ne_zero (MvPolynomial.C_ne_zero.mpr (mul_ne_zero h4 hA)) ?_
  intro h0
  have hc : (C (azA a b) * X 1 ^ 2 + C (azB a b) : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 2) = azA a b := by
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
      MvPolynomial.coeff_C_of_ne_zero (by simp [Finsupp.single_eq_zero])]
    simp
  rw [h0, MvPolynomial.coeff_zero] at hc
  exact hA hc.symm

end Work.MotAS
