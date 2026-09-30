import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- The first difference of a polynomial over `ℚ` along the shift `X ↦ X - k` (`k ≥ 1`): for
`P = ∑ aᵢ X^i` the leading terms cancel, `P - P(X-k) = aᵣ (Xʳ - (X-k)ʳ) + (lower) = aᵣ r k X^{r-1} + …`,
so the `natDegree` drops by exactly one (with the convention `0 - 1 = 0` in `ℕ`, which is correct
here because `natDegree P = 0` makes `P` a constant and `P - P(X-k) = 0`).

Equivalently: `(P - P.comp (X - C k)).natDegree = P.natDegree - 1`. Suggested proof: from
`Polynomial.eq_C_of_natDegree_eq_zero` in the degree-`0` case, and for `r = P.natDegree ≥ 1`
write `P = C a * X^r + R` with `natDegree R < r`, then use `coeff` computations /
`Polynomial.natDegree_sub_lt_of_natDegree_eq`, together with
`(X - C k)^r = ∑_{i ≤ r} C(r,i) (-k)^{r-i} X^i` (`add_pow`) to see that the coefficient of
`X^{r-1}` in `P - P(X-k)` is `a r k ≠ 0`. -/
theorem poly_shift_natDegree (P : Polynomial ℚ) (k : ℕ) (hk : 1 ≤ k) :
    (P - P.comp (Polynomial.X - Polynomial.C (k : ℚ))).natDegree = P.natDegree - 1 := by
  set q : Polynomial ℚ := Polynomial.X - Polynomial.C (k : ℚ) with hqdef
  have hq : q = Polynomial.X + Polynomial.C (-(k : ℚ)) := by
    rw [hqdef, sub_eq_add_neg, map_neg]
  -- `P.comp q` is the Taylor shift of `P` by `-(k : ℚ)`, so `taylor_coeff` computes its
  -- coefficients as evaluations of Hasse derivatives.
  have hcomp : P.comp q = taylor (-(k : ℚ)) P := by rw [hq, taylor_apply]
  have hcoeff : ∀ m, (P.comp q).coeff m = (hasseDeriv m P).eval (-(k : ℚ)) := by
    intro m; rw [hcomp, taylor_coeff]
  rcases Nat.eq_zero_or_pos P.natDegree with hr | hr
  · -- degree `0`: `P` is constant, so the difference is `0`.
    have hP : P = Polynomial.C (P.coeff 0) := eq_C_of_natDegree_eq_zero hr
    rw [hP]
    simp
  · have hr1 : 1 ≤ P.natDegree := hr
    -- Upper bound: all coefficients of degree `≥ P.natDegree` vanish in the difference.
    have hle : (P - P.comp q).natDegree ≤ P.natDegree - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hNd : P.natDegree ≤ N := by omega
      rw [coeff_sub, hcoeff N]
      rcases lt_or_eq_of_le hNd with hlt | heq
      · rw [coeff_eq_zero_of_natDegree_lt hlt, hasseDeriv_eq_zero_of_lt_natDegree P N hlt]
        simp
      · subst heq
        rw [hasseDeriv_natDegree_eq_C, coeff_natDegree, eval_C, sub_self]
    refine natDegree_eq_of_le_of_coeff_ne_zero hle ?_
    -- The Hasse derivative of order `P.natDegree - 1` has degree `≤ 1`, so its evaluation
    -- is controlled by its two lowest coefficients.
    have heval : (hasseDeriv (P.natDegree - 1) P).eval (-(k:ℚ))
        = P.coeff (P.natDegree - 1) + (P.natDegree : ℚ) * P.coeff P.natDegree * (-(k:ℚ)) := by
      have hnd : (hasseDeriv (P.natDegree - 1) P).natDegree < 2 := by
        have := natDegree_hasseDeriv_le P (P.natDegree - 1); omega
      rw [eval_eq_sum_range' hnd]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rw [show (hasseDeriv (P.natDegree - 1) P).coeff 0 = P.coeff (P.natDegree - 1) from by
            rw [hasseDeriv_coeff]; simp,
          show (hasseDeriv (P.natDegree - 1) P).coeff 1 = (P.natDegree : ℚ) * P.coeff P.natDegree from by
            rw [hasseDeriv_coeff]
            have h1 : 1 + (P.natDegree - 1) = P.natDegree := by omega
            rw [h1]
            have h2 : Nat.choose P.natDegree (P.natDegree - 1) = P.natDegree := by
              have := Nat.choose_succ_self_right (P.natDegree - 1)
              rwa [Nat.sub_add_cancel hr1] at this
            rw [h2]]
      ring
    -- The coefficient of `X^{P.natDegree - 1}` is exactly `P.natDegree * k * (leading coeff)`.
    have hval : (P - P.comp q).coeff (P.natDegree - 1)
        = (P.natDegree : ℚ) * (k:ℚ) * P.coeff P.natDegree := by
      rw [coeff_sub, hcoeff (P.natDegree - 1), heval]
      ring
    rw [hval]
    have hk0 : (k:ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hr0 : (P.natDegree : ℚ) ≠ 0 := by exact_mod_cast (by omega : P.natDegree ≠ 0)
    have hlk : P.coeff P.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hr)
    exact mul_ne_zero (mul_ne_zero hr0 hk0) hlk

end Work.BW
