import Mathlib
import Submission.Work.C17.local_tools

/-!
# The local expansion of `P₁Q / P₂Q` at `x = 0`

`P₂x = (X−1)·X·(X+1)·Q4x` vanishes to order exactly one at `X = 0` and `P₁x(0) = −1`, so
`P₁Q a b / P₂Q a b = x^{-1}·(1 − 4ab·x + O(x²))` there.  This is the last entry of the
conjunction `Work.C17.local_base` used by `Work.C17.order3_class_injective`.

The proof writes `P₂x = X·u` with `u(0) = −1 ≠ 0`, and `P₁x − u + 4ab·X·u = X²·R` with an
explicit polynomial `R`; then the master reduction `lead2At_of_eq` with
`g = algP R / algP u` (`Reg g` because `u` is a unit at `0`) gives the claim.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc Polynomial

noncomputable section

local notation "algP" => algebraMap (Polynomial ℚ) (RatFunc ℚ)

set_option maxHeartbeats 1000000 in
/-- **The lemma.**  `P₁Q a b / P₂Q a b = x^{-1}·(1 − 4ab·x + O(x²))` at `x = 0`. -/
theorem lead2_ratio (a b : ℚ) : Lead2At (P1Q a b / P2Q a b) (-1) 1 (-4 * a * b) := by
  set u : Polynomial ℚ := (X - 1) * (X + 1) * Q4x a b with hu
  set R : Polynomial ℚ :=
    Polynomial.C (16 * a ^ 2 * b ^ 2 - 8 * a ^ 2 - 8 * b ^ 2 + 2)
      - Polynomial.C (16 * a ^ 3 * b + 16 * a * b ^ 3 - 28 * a * b) * X
      - 4 * X ^ 2
      + Polynomial.C (16 * a ^ 3 * b + 16 * a * b ^ 3 - 16 * a * b) * X ^ 3
      + Polynomial.C (-16 * a ^ 2 * b ^ 2 + 2) * X ^ 4
      + Polynomial.C (4 * a * b) * X ^ 5 with hR
  set M : Polynomial ℚ := P1x a b - u + Polynomial.C (4 * a * b) * X * u with hM
  -- `u` is a unit at `0` (it equals `-1` there)
  have hu0 : u.coeff 0 = -1 := by
    rw [hu, Polynomial.coeff_zero_eq_eval_zero]; simp [Q4x]
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, Polynomial.coeff_zero] at hu0; norm_num at hu0
  -- `P₂ = X·u`
  have hP2 : P2x a b = X * u := by rw [P2x, hu]; ring
  -- `M = X²·R`
  have hMR : M = X ^ 2 * R := by
    rw [hM, hR, hu]
    apply Polynomial.funext; intro x
    simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_one, eval_neg,
      eval_ofNat, P1x, Q4x]
    ring
  have hu_alg : algP u ≠ 0 := algP_ne_zero hu_ne
  refine lead2At_of_eq (P1Q a b / P2Q a b) (-1) 1 (-4 * a * b) one_ne_zero
    (g := algP R / algP u)
    (reg_div_algebraMap_local_tools (p := R) (q := u) (by rw [hu0]; norm_num)) ?_
  have hAlg : algP M = xQ ^ 2 * algP R := by
    rw [hMR, map_mul, map_pow, xQ_eq_algP]
  have hp2e : P2Q a b = xQ * algP u := by rw [P2Q, hP2, map_mul, xQ_eq_algP]
  have hcancel : algP (P1x a b) / (xQ * algP u) * xQ = algP (P1x a b) / algP u := by
    rw [div_mul_eq_mul_div, mul_comm (algP (P1x a b)) xQ,
      mul_div_mul_left (algP (P1x a b)) (algP u) xQ_ne_zero_local_tools]
  -- the identity, after multiplying by the denominator `u`
  have hmain : (P1Q a b / P2Q a b * xQ - algebraMap ℚ (RatFunc ℚ) 1
      - algebraMap ℚ (RatFunc ℚ) (-4 * a * b) * xQ) * algP u = algP M := by
    rw [P1Q, hp2e, hcancel, map_one,
      show (-4 * a * b : ℚ) = -(4 * a * b) by ring, map_neg, algQ_eq_algP (4 * a * b)]
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hu_alg, one_mul, neg_mul, neg_mul]
    rw [sub_neg_eq_add, xQ_eq_algP, hM]
    simp only [← map_mul, ← map_add, ← map_sub]
  rw [neg_neg, zpow_one]
  apply mul_right_cancel₀ (b := algP u) hu_alg
  have h2 : xQ ^ 2 * (algP R / algP u) * algP u = xQ ^ 2 * algP R := by
    rw [mul_assoc, div_mul_cancel₀ _ hu_alg]
  rw [h2]
  exact hmain.trans hAlg

end

end Work.C17
