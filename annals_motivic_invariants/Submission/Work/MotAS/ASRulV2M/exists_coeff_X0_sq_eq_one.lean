import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASRulV2M.coeff_X0_sq_combination

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.exists_coeff_X0_sq_eq_one`

Part of the height computation for the AS residual chart ideal `ZIAS a b g`
(`Work.MotAS.ASRulV2M.height_radical_ZIAS`).

It is proved here that `ZIAS a b g` contains an element whose `X₀²`-coefficient is `1`: the
`K`-multiple `(2s⁵)⁻¹ (s·zcubAS a b g 2 − (s+b)·zcubAS a b g 4)` of the two-generator combination
`s·C₂ − (s+b)·C₄`, `s = a - 3b`, whose `X₀²`-coefficient is `2s⁵` by
`Work.MotAS.ASRulV2M.coeff_X0_sq_combination`.

Consequence used downstream: in the quotient `K[X₀,X₁,X₂] ⧸ ZIAS a b g` the class of `X₀` satisfies
a monic quadratic relation with coefficients in the image of `K[X₁,X₂]`; hence that quotient is a
finite module over `K[X₁,X₂] ⧸ (ZIAS a b g ∩ K[X₁,X₂])` and has the same Krull dimension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- **`ZIAS a b g` contains an element which is monic of degree `2` in `X₀`.**

More precisely some `F ∈ ZIAS a b g` has `X₀²`-coefficient `1`.  The element is
`(2s⁵)⁻¹ (s·C₂ − (s+b)·C₄)` with `s = a - 3b`. -/
theorem exists_coeff_X0_sq_eq_one (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hA : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    ∃ F ∈ Work.MotAS.ZIAS a b g,
      F.coeff (Finsupp.single (0 : Fin 3) 2) = 1 := by
  classical
  -- `s = a - 3b` is nonzero because `s^2 = a^2 - a*b - b^2` in characteristic `5`.
  have hkey : (a - 3 * b) ^ 2 = a ^ 2 - a * b - b ^ 2 := by
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have h' : (a - 3 * b) ^ 2 - (a ^ 2 - a * b - b ^ 2) = 5 * (2 * b ^ 2 - a * b) := by ring
    rw [← sub_eq_zero, h', h5, zero_mul]
  have hs0 : a - 3 * b ≠ 0 := by
    intro h
    exact hA (by rw [← hkey, h]; ring)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h
    norm_num at hd
  have hc : 2 * (a - 3 * b) ^ 5 ≠ 0 := mul_ne_zero h2 (pow_ne_zero 5 hs0)
  refine ⟨MvPolynomial.C (2 * (a - 3 * b) ^ 5)⁻¹ *
      (MvPolynomial.C (a - 3 * b) * Work.MotAS.zcubAS a b g 2
        - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.zcubAS a b g 4), ?_, ?_⟩
  · refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ ?_)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨2, rfl⟩)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩)
  · rw [MvPolynomial.coeff_C_mul, coeff_X0_sq_combination, inv_mul_cancel₀ hc]

end Work.MotAS.ASRulV2M
