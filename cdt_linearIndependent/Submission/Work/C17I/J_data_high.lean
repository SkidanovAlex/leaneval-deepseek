import Mathlib
import Submission.Work.C17.seventeen_defs

/-!
# The numerator/denominator data for the "high" integrals `y ^ (i-4) · dy`, `3 ≤ i ≤ 5`

For `i : Fin 6` with `3 ≤ i`, the exponent `(i : ℤ) - 4` is `-1`, `0` or `1`, and the rational
function `yQ ^ ((i:ℤ)-4) * dyQ ∈ ℚ(x)` (with `yQ = x²/(x-1)` and `dyQ = (x²-2x)/(x-1)²` the
`RatFunc ℚ` models of `y` and `dy/dx`) has a presentation `P/Q` with `Q` non-vanishing on any
`U ⊆ ℂ \ {0,1}`, and with the value identity
`P(z)/Q(z) = y(z) ^ ((i:ℤ)-4) · (z²-2z)/(z-1)²` for `z ∈ U`.

The explicit reduced forms of `y ^ k · dy`, `k = -1, 0, 1`, are

* `k = -1`: `(x-2)/(x(x-1))`,
* `k =  0`: `x(x-2)/(x-1)²`,
* `k =  1`: `x³(x-2)/(x-1)³`,

whose denominators vanish only at `x = 0` and `x = 1`; this is what makes the "high" indices
easier than the "low" ones (`J_data_low`).
-/

namespace Work.C17I

open Polynomial

/-- For `i ∈ {3,4,5}` the rational function `yQ ^ ((i:ℤ)-4) * dyQ` has an explicit
numerator/denominator presentation over `ℚ` whose denominator is non-vanishing on any
`U ⊆ ℂ \ {0,1}`. -/
theorem J_data_high (i : Fin 6) (hi : 3 ≤ (i : ℕ)) {U : Set ℂ}
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (∀ z ∈ U, Q.eval₂ (algebraMap ℚ ℂ) z ≠ 0) ∧
      Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) P / algebraMap (Polynomial ℚ) (RatFunc ℚ) Q ∧
      (∀ z ∈ U, P.eval₂ (algebraMap ℚ ℂ) z / Q.eval₂ (algebraMap ℚ ℂ) z
        = Work.C17.yC z ^ ((i : ℤ) - 4) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2)) := by
  fin_cases i <;> simp only [] at hi ⊢
  · omega
  · omega
  · omega
  · -- `i = 3`: exponent `-1`, reduced form `(x-2)/(x(x-1))`
    have hk : (((3 : ℕ) : ℤ)) - 4 = (-1 : ℤ) := by norm_num
    rw [hk]
    refine ⟨Polynomial.X - 2, Polynomial.X * (Polynomial.X - 1), ?_, ?_, ?_, ?_⟩
    · -- `X * (X - 1) ≠ 0`
      apply mul_ne_zero Polynomial.X_ne_zero
      rw [sub_ne_zero]
      exact Polynomial.X_ne_C 1
    · -- `z * (z - 1) ≠ 0` on `U`
      intro z hz
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_one]
      exact mul_ne_zero (h0 z hz) (sub_ne_zero.mpr (h1 z hz))
    · -- the `ℚ(x)`-identity
      rw [zpow_neg_one, Work.C17.yQ, Work.C17.dyQ, Work.C17.xQ]
      simp only [map_sub, map_mul, map_ofNat, map_one, RatFunc.algebraMap_X]
      field_simp
    · -- the value identity
      intro z hz
      rw [zpow_neg_one, Work.C17.yC]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
      field_simp [h0 z hz, sub_ne_zero.mpr (h1 z hz)]
  · -- `i = 4`: exponent `0`, reduced form `x(x-2)/(x-1)²`
    have hk : (((4 : ℕ) : ℤ)) - 4 = (0 : ℤ) := by norm_num
    rw [hk]
    refine ⟨Polynomial.X * (Polynomial.X - 2), (Polynomial.X - 1) ^ 2, ?_, ?_, ?_, ?_⟩
    · exact pow_ne_zero 2 (by rw [sub_ne_zero]; exact Polynomial.X_ne_C 1)
    · intro z hz
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Polynomial.eval₂_pow]
      exact pow_ne_zero 2 (sub_ne_zero.mpr (h1 z hz))
    · rw [zpow_zero, one_mul, Work.C17.dyQ, Work.C17.xQ]
      simp only [map_sub, map_mul, map_pow, map_ofNat, map_one, RatFunc.algebraMap_X]
      field_simp
    · intro z hz
      rw [zpow_zero, one_mul]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Polynomial.eval₂_ofNat, Polynomial.eval₂_pow]
      ring
  · -- `i = 5`: exponent `1`, reduced form `x³(x-2)/(x-1)³`
    have hk : (((5 : ℕ) : ℤ)) - 4 = (1 : ℤ) := by norm_num
    rw [hk]
    refine ⟨Polynomial.X ^ 3 * (Polynomial.X - 2), (Polynomial.X - 1) ^ 3, ?_, ?_, ?_, ?_⟩
    · exact pow_ne_zero 3 (by rw [sub_ne_zero]; exact Polynomial.X_ne_C 1)
    · intro z hz
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Polynomial.eval₂_pow]
      exact pow_ne_zero 3 (sub_ne_zero.mpr (h1 z hz))
    · rw [zpow_one, Work.C17.yQ, Work.C17.dyQ, Work.C17.xQ]
      simp only [map_sub, map_mul, map_pow, map_ofNat, map_one, RatFunc.algebraMap_X]
      field_simp
    · intro z hz
      rw [zpow_one, Work.C17.yC]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Polynomial.eval₂_ofNat, Polynomial.eval₂_pow]
      field_simp [h1 z hz]

end Work.C17I
