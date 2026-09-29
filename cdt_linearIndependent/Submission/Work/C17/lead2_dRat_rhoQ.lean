import Mathlib
import Submission.Work.C17.local_tools

/-!
# Local data of `dRat rhoQ` at `x = 0`

`rhoQ = (x-1)²/(x²-2x) = dx/dy` is the multiplier turning `∂_x` into `∂_y`
(see `Submission.Work.C17.seventeen_indep`).  Writing `p = (X-1)²`, `q = X²-2X`,
one has `rhoQ = p/q`, and the quotient rule gives

  `dRat rhoQ = (p'q - pq')/q² = (2-2x)/(x²(x-2)²) = -2(x-1)/(x²(x-2)²)`.

Consequently `dRat rhoQ = x⁻²·(1/2 + 0·x + O(x²))`, since

  `dRat rhoQ · x² - 1/2 = -2(x-1)/(x-2)² - 1/2 = -x²/(2(x-2)²)`,

and `-1/(2(x-2)²)` is regular at `0` (its denominator does not vanish there).
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc Polynomial

noncomputable section

/-- `xQ - 2` is the image of the polynomial `X - 2`, hence does not vanish at `0`. -/
private lemma xQ_sub_two_eq_algebraMap :
    (xQ - 2 : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 2) := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap]
  simp only [map_sub, map_ofNat, aeval_X]
  rfl

/-- **Local expansion of `dRat rhoQ` at `x = 0`:** the leading term at `x = 0` is
`(1/2)·x⁻²`, the next coefficient is `0`. -/
theorem lead2_dRat_rhoQ : Lead2At (Submission.CDT.dRat rhoQ) (-2) (1/2) 0 := by
  -- `rhoQ = p/q` with `p = (X-1)²`, `q = X² - 2X`.
  have hp : algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.X - 1) ^ 2) = (xQ - 1) ^ 2 := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    simp only [map_pow, map_sub, map_one, aeval_X]
    rfl
  have hq : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 2 - 2 * Polynomial.X)
      = (xQ ^ 2 - 2 * xQ) := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    simp only [map_sub, map_pow, map_mul, map_ofNat, aeval_X]
    rfl
  -- the quotient-rule numerator `p'q - pq' = 2 - 2X`
  have hder : ((Polynomial.X - 1 : Polynomial ℚ) ^ 2).derivative
        * (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ)
      - (Polynomial.X - 1 : Polynomial ℚ) ^ 2
        * (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ).derivative
      = 2 - 2 * Polynomial.X := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_ofNat]
    norm_num [Polynomial.C_ofNat]
    ring
  have hnum : algebraMap (Polynomial ℚ) (RatFunc ℚ) (2 - 2 * Polynomial.X)
      = (2 - 2 * xQ : RatFunc ℚ) := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    simp only [map_sub, map_mul, map_ofNat, aeval_X]
    rfl
  have hrhoQ : rhoQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.X - 1) ^ 2)
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 2 - 2 * Polynomial.X) := by
    rw [rhoQ, ← hp, ← hq]
  -- the value of `dRat rhoQ`
  have hD : Submission.CDT.dRat rhoQ = -2 * (xQ - 1) / (xQ ^ 2 * (xQ - 2) ^ 2) := by
    have hd := Submission.CDT.dRat_div (K := ℚ)
      ((Polynomial.X - 1 : Polynomial ℚ) ^ 2)
      (Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ)
    rw [← hrhoQ] at hd
    rw [hder] at hd
    rw [hd, hnum, hq]
    field_simp
    ring
  have hx2ne : (xQ - 2 : RatFunc ℚ) ≠ 0 := by
    rw [xQ_sub_two_eq_algebraMap]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (2 : ℚ))
  have hxne : (xQ : RatFunc ℚ) ≠ 0 := xQ_ne_zero_local_tools
  -- master reduction: exhibit a regular `g` with `dRat rhoQ · x² - 1/2 = x² · g`
  refine lead2At_of_eq _ _ _ _ (by norm_num) (g := -(1/2) / (xQ - 2) ^ 2) ?_ ?_
  · -- `-(1/2)/(x-2)²` is the image of `C(-1/2)/(X-2)²`, hence regular at `0`
    have h1 : (-(1 / 2) : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) (-(1 / 2)) := by norm_num
    rw [h1, xQ_sub_two_eq_algebraMap, ← map_pow, algQ_eq_algP]
    exact reg_div_algebraMap_local_tools (p := Polynomial.C (-(1 / 2))) (by
      rw [Polynomial.coeff_zero_eq_eval_zero]; norm_num)
  · -- the identity `dRat rhoQ · x² - 1/2 = x² · g`
    have hhalf : algebraMap ℚ (RatFunc ℚ) (1 / 2) = (1 / 2 : RatFunc ℚ) := by norm_num
    rw [show (-(-2) : ℤ) = 2 from by norm_num, zpow_ofNat, hD, hhalf]
    simp only [map_zero, zero_mul, sub_zero]
    field_simp
    ring

end

end Work.C17
