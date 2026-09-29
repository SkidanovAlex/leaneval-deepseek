import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_div
import Submission.Commons.FieldTheory.RatFunc.ordAtT_algebraMap

namespace Commons.FieldTheory.RatFunc

/-- A quotient `p/q` of polynomials in which `q` does not vanish at `α` is *regular* at `α`: its order there is nonnegative.  This is the elementary input that lets the local/indicial analysis of the CDT operators (`Σᵢ (−1)ⁱ Dⁱ(γᵢ b)` with `γᵢ = cᵢ/c₄`) be applied at the non-singular points: away from the zeros of the common denominator `c₄`, every `γᵢ` is regular. -/
theorem zero_le_ordAtT_div_of_eval_ne_zero {K : Type*} [Field K] {p q : Polynomial K} {α : K}
    (hq : q.eval α ≠ 0) :
    (0 : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) p
      / algebraMap (Polynomial K) (RatFunc K) q) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [map_zero, zero_div]
    simp [ordAtT]
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, Polynomial.eval_zero])
  have hrm : Polynomial.rootMultiplicity α q = 0 :=
    Polynomial.rootMultiplicity_eq_zero (fun h => hq h)
  have hp0 : algebraMap (Polynomial K) (RatFunc K) p ≠ 0 := fun h =>
    hp (IsFractionRing.injective (Polynomial K) (RatFunc K) (by simpa using h))
  have hq0' : algebraMap (Polynomial K) (RatFunc K) q ≠ 0 := fun h =>
    hq0 (IsFractionRing.injective (Polynomial K) (RatFunc K) (by simpa using h))
  rw [ordAtT_div α hp0 hq0', ordAtT_algebraMap hp, ordAtT_algebraMap hq0, hrm]
  simp

end Commons.FieldTheory.RatFunc
