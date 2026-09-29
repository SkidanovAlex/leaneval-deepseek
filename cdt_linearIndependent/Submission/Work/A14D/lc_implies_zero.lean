import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.chainZDefs
import Submission.Work.A14D.chainZ_ana
import Submission.Work.A14D.chainZ_rat
import Submission.Work.A14D.riccatiZ_no_rational
import Submission.Work.A14D.adjointZ_no_solution
import Submission.Work.A14D.classZ_injective
import Submission.Work.GenShared.periods_indep_gen
import Submission.Work.C17.exists_cleared_pAtY

/-!
# `lc_implies_zero` : the algebraic endgame of the `A14` route

Given the holomorphic solution `y9` of Zagier's operator `L_Z` at the singular point `x = 1/9`
and primitives `J_i` of `r_i y9` (`r_i = y^{-i} y'`, `y = x²/(x-1)`), any relation
`Σ_k p_k(y(x)) ∂_y^k y9 + Σ_i q_i(y(x)) J_i = 0` with polynomial coefficients `p_k, q_i` forces
`p = q = 0`.

The proof reduces the relation to a *polynomial-coefficient* one on a small disc inside
`ball (1/9) δ` (clearing the denominators of the classes `clsZ k` and of `p_k(y(x))`), applies the
generic period-independence theorem `Work.GenShared.periods_indep_gen` (with the Riccati and
adjoint certificates `riccatiZ_no_rational`, `adjointZ_no_solution`), and then inverts the
clearing to reach the `ℚ(x)`-module relation among the classes `clsZ k`, which
`classZ_injective` turns into `p = 0`.  The periods part gives `q = 0` directly.
-/

namespace Work.A14D

open Complex Metric Polynomial
open scoped BigOperators

/-- The multiplier turning `DZpoly k` into `DZpoly 3`. -/
noncomputable def lcizE (k : Fin 4) : Polynomial ℚ := (pZq * wXq) ^ (7 - (2 ^ (k : ℕ) - 1))

lemma lcizE_mul (k : Fin 4) : lcizE k * DZpoly (k : ℕ) = DZpoly 3 := by
  have hk : (k : ℕ) ≤ 3 := by omega
  have h2 : 2 ^ (k : ℕ) - 1 ≤ 7 := by
    have h3 : 2 ^ (k : ℕ) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [lcizE, DZpoly_eq, DZpoly_eq, show (2 : ℕ) ^ 3 - 1 = 7 from by norm_num,
    ← pow_add, Nat.sub_add_cancel h2]

/-- The cleared `y9`-coefficient polynomial of the relation. -/
noncomputable def lcizA (dg : ℕ) (pp : Fin 4 → Polynomial ℚ) : Polynomial ℚ :=
  ∑ k : Fin 4, Work.C17.clearedAtY (pp k) dg * lcizE k * AZpoly (k : ℕ)

/-- The cleared `y9'`-coefficient polynomial of the relation. -/
noncomputable def lcizB (dg : ℕ) (pp : Fin 4 → Polynomial ℚ) : Polynomial ℚ :=
  ∑ k : Fin 4, Work.C17.clearedAtY (pp k) dg * lcizE k * BZpoly (k : ℕ)

/-- The cleared `J`-coefficient polynomials of the relation. -/
noncomputable def lcizC (dg : ℕ) (qq : Fin 3 → Polynomial ℚ) : Fin 3 → Polynomial ℚ :=
  fun i => Work.C17.clearedAtY (qq i) dg * DZpoly 3

/-! ## The small disc

All the exceptional points `0, 1, 2` of the operator data (and the singular point `1/9` itself) lie
outside `ball (c) (η/2)` with `c = 1/9 + η/2`. -/

lemma lciz_ninth_cast : ninth = ((1 / 9 : ℝ) : ℂ) := by norm_num [ninth]

lemma lciz_ball_sub {η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ / 2) {z : ℂ}
    (hz : z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2)) : z ∈ ball ninth δ := by
  rw [lciz_ninth_cast]
  rw [mem_ball, dist_eq] at hz ⊢
  have hnorm : ‖(((1 / 9 + η / 2 : ℝ) : ℂ) - ((1 / 9 : ℝ) : ℂ))‖ = η / 2 := by
    have hcast : ((1 / 9 + η / 2 : ℝ) : ℂ) - ((1 / 9 : ℝ) : ℂ) = ((η / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, show ‖((η / 2 : ℝ) : ℂ)‖ = |η / 2| from RCLike.norm_ofReal (η / 2),
      abs_of_pos (by linarith : (0 : ℝ) < η / 2)]
  have hsplit : z - ((1 / 9 : ℝ) : ℂ)
      = (z - ((1 / 9 + η / 2 : ℝ) : ℂ)) + (((1 / 9 + η / 2 : ℝ) : ℂ) - ((1 / 9 : ℝ) : ℂ)) := by
    ring
  calc ‖z - ((1 / 9 : ℝ) : ℂ)‖
      = ‖(z - ((1 / 9 + η / 2 : ℝ) : ℂ)) + (((1 / 9 + η / 2 : ℝ) : ℂ) - ((1 / 9 : ℝ) : ℂ))‖ := by
        rw [hsplit]
    _ ≤ ‖z - ((1 / 9 + η / 2 : ℝ) : ℂ)‖ + ‖(((1 / 9 + η / 2 : ℝ) : ℂ) - ((1 / 9 : ℝ) : ℂ))‖ :=
        norm_add_le _ _
    _ < η / 2 + η / 2 := by rw [hnorm]; linarith
    _ = η := by ring
    _ ≤ δ := by linarith

lemma lciz_ne_ninth {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2)) : z ≠ ninth := by
  intro h
  rw [lciz_ninth_cast] at h
  rw [mem_ball, dist_eq, h] at hz
  have hnorm : ‖(((1 / 9 : ℝ) : ℂ) - ((1 / 9 + η / 2 : ℝ) : ℂ))‖ = η / 2 := by
    have hcast : ((1 / 9 : ℝ) : ℂ) - ((1 / 9 + η / 2 : ℝ) : ℂ) = ((-(η / 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, show ‖((-(η / 2) : ℝ) : ℂ)‖ = |-(η / 2)| from RCLike.norm_ofReal (-(η / 2)),
      abs_neg, abs_of_pos (by linarith : (0 : ℝ) < η / 2)]
  rw [hnorm] at hz
  linarith

lemma lciz_ne_zero {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2)) : z ≠ 0 := by
  intro h
  rw [mem_ball, dist_eq, h, zero_sub, norm_neg] at hz
  have hnorm : ‖(((1 / 9 + η / 2 : ℝ) : ℂ))‖ = 1 / 9 + η / 2 := by
    rw [show ‖(((1 / 9 + η / 2 : ℝ) : ℂ))‖ = |(1 / 9 + η / 2)| from
        RCLike.norm_ofReal (1 / 9 + η / 2),
      abs_of_pos (by linarith : (0 : ℝ) < 1 / 9 + η / 2)]
  rw [hnorm] at hz
  linarith

lemma lciz_ne_one {η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ / 2) (hδ : δ ≤ 1 / 20) {z : ℂ}
    (hz : z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2)) : z ≠ 1 := by
  intro h
  rw [mem_ball, dist_eq, h] at hz
  have hnorm : ‖(1 : ℂ) - ((1 / 9 + η / 2 : ℝ) : ℂ)‖ = 8 / 9 - η / 2 := by
    have hcast : (1 : ℂ) - ((1 / 9 + η / 2 : ℝ) : ℂ) = ((8 / 9 - η / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, show ‖((8 / 9 - η / 2 : ℝ) : ℂ)‖ = |8 / 9 - η / 2| from RCLike.norm_ofReal _,
      abs_of_pos (by linarith : (0 : ℝ) < 8 / 9 - η / 2)]
  rw [hnorm] at hz
  linarith

lemma lciz_ne_two {η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ / 2) (hδ : δ ≤ 1 / 20) {z : ℂ}
    (hz : z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2)) : z ≠ 2 := by
  intro h
  rw [mem_ball, dist_eq, h] at hz
  have hnorm : ‖(2 : ℂ) - ((1 / 9 + η / 2 : ℝ) : ℂ)‖ = 17 / 9 - η / 2 := by
    have hcast : (2 : ℂ) - ((1 / 9 + η / 2 : ℝ) : ℂ) = ((17 / 9 - η / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, show ‖((17 / 9 - η / 2 : ℝ) : ℂ)‖ = |17 / 9 - η / 2| from RCLike.norm_ofReal _,
      abs_of_pos (by linarith : (0 : ℝ) < 17 / 9 - η / 2)]
  rw [hnorm] at hz
  linarith

/-! ## Two bridges with the `J`-data -/

/-- `rnC i / rdC i` is the rational function `rQc i = y^{-i} y'`. -/
lemma lciz_rQc_eq (i : Fin 3) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (rnC i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rdC i) = rQc i := by
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hX1 : (RatFunc.X - 1 : RatFunc ℂ) ≠ 0 := by
    rw [show (RatFunc.X - 1 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.X - 1) by rw [map_sub, map_one, RatFunc.algebraMap_X]]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · simp only [rnC, rdC, rQc, yQc, dyQc]
    simp
  · simp only [rnC, rdC, rQc, yQc, dyQc]
    simp
    field_simp
  · simp only [rnC, rdC, rQc, yQc, dyQc]
    simp
    field_simp

/-- The derivative datum `(yC z)^{-i} dyC z` is `(rnC i).eval z / (rdC i).eval z`. -/
lemma lciz_deriv_coeff (i : Fin 3) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (yC z)⁻¹ ^ (i : ℕ) * dyC z = (rnC i).eval z / (rdC i).eval z := by
  fin_cases i <;> simp [rnC, rdC, yC, dyC] <;> field_simp

/-! ## Clearing the coefficient `p(yC z)` -/

lemma lciz_clearedAtY_eval (pp : Polynomial ℚ) (dg : ℕ) (hd : pp.natDegree ≤ dg) {z : ℂ}
    (hz : z ≠ 1) : (z - 1) ^ dg * pAtY pp z = (Work.C17.clearedAtY pp dg).eval₂ (algebraMap ℚ ℂ) z := by
  have hpow : ∀ k ≤ dg, (z - 1) ^ dg * yC z ^ k = z ^ (2 * k) * (z - 1) ^ (dg - k) := by
    intro k hk
    have h1 : (z - 1) * yC z = z ^ 2 := by rw [yC]; field_simp
    calc (z - 1) ^ dg * yC z ^ k
        = ((z - 1) ^ (dg - k) * (z - 1) ^ k) * yC z ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
      _ = (z - 1) ^ (dg - k) * ((z - 1) ^ k * yC z ^ k) := by ring
      _ = (z - 1) ^ (dg - k) * ((z - 1) * yC z) ^ k := by rw [mul_pow]
      _ = (z - 1) ^ (dg - k) * (z ^ 2) ^ k := by rw [h1]
      _ = z ^ (2 * k) * (z - 1) ^ (dg - k) := by rw [pow_mul]; ring
  have hp1 : pAtY pp z = ∑ k ∈ Finset.range (dg + 1), (algebraMap ℚ ℂ (pp.coeff k)) * yC z ^ k := by
    rw [pAtY, Polynomial.eval₂_eq_sum_range' (algebraMap ℚ ℂ) (n := dg + 1) (by omega)]
  rw [hp1, Finset.mul_sum]
  simp only [Work.C17.clearedAtY, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_one]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ dg := Nat.lt_succ_iff.mp hk
  rw [show (z - 1) ^ dg * ((algebraMap ℚ ℂ) (pp.coeff k) * yC z ^ k)
        = (algebraMap ℚ ℂ) (pp.coeff k) * ((z - 1) ^ dg * yC z ^ k) by ring,
    hpow k hk']
  ring

lemma lciz_clearedAtY_eq_zero_iff (pp : Polynomial ℚ) (dg : ℕ) (hd : pp.natDegree ≤ dg) :
    Work.C17.clearedAtY pp dg = 0 ↔ pp = 0 := by
  constructor
  · intro h
    by_contra hp
    have hc := Work.C17.coeff_clearedAtY pp dg hd
    rw [h, Polynomial.coeff_zero] at hc
    refine hp (Polynomial.leadingCoeff_eq_zero.mp ?_)
    rw [← Polynomial.coeff_natDegree]
    exact hc.symm
  · intro hp
    rw [hp]
    simp [Work.C17.clearedAtY]

/-- The bridge from the cleared polynomial to the rational function `(z-1)^dg p(yC z)`. -/
lemma lciz_clearedAtY_algebraMap (pp : Polynomial ℚ) (dg : ℕ) (hd : pp.natDegree ≤ dg) :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY pp dg)
      = (RatFunc.X - 1) ^ dg * pp.eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs := by
  have hne : (RatFunc.X - 1 : RatFunc ℚ) ≠ 0 := by
    intro h
    have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) = 0 := by
      rw [map_sub, map_one]; exact h
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1) h1
  have hkey : ∀ k : ℕ, k ≤ dg →
      (RatFunc.X - 1 : RatFunc ℚ) ^ dg * (RatFunc.X ^ 2 / (RatFunc.X - 1)) ^ k
        = RatFunc.X ^ (2 * k) * (RatFunc.X - 1) ^ (dg - k) := by
    intro k hk
    have h2 : (RatFunc.X ^ 2 / (RatFunc.X - 1) : RatFunc ℚ) ^ k * (RatFunc.X - 1) ^ k
        = RatFunc.X ^ (2 * k) := by
      rw [← mul_pow, div_mul_cancel₀ (RatFunc.X ^ 2) hne, ← pow_mul]
    calc (RatFunc.X - 1 : RatFunc ℚ) ^ dg * (RatFunc.X ^ 2 / (RatFunc.X - 1)) ^ k
        = ((RatFunc.X - 1) ^ (dg - k) * (RatFunc.X - 1) ^ k)
            * (RatFunc.X ^ 2 / (RatFunc.X - 1)) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
      _ = (RatFunc.X - 1) ^ (dg - k)
            * ((RatFunc.X ^ 2 / (RatFunc.X - 1)) ^ k * (RatFunc.X - 1) ^ k) := by ring
      _ = (RatFunc.X - 1) ^ (dg - k) * RatFunc.X ^ (2 * k) := by rw [h2]
      _ = RatFunc.X ^ (2 * k) * (RatFunc.X - 1) ^ (dg - k) := by ring
  rw [Polynomial.eval₂_eq_sum_range' (algebraMap ℚ (RatFunc ℚ)) (n := dg + 1) (by omega)]
  rw [Work.C17.clearedAtY, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ dg := Nat.lt_succ_iff.mp hk
  simp only [map_mul, map_pow, map_sub, map_one, yQs, xQ', RatFunc.algebraMap_X]
  rw [show (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.C (pp.coeff k))
        = (algebraMap ℚ (RatFunc ℚ)) (pp.coeff k) from by
      rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ)
        (RatFunc ℚ)]]
  rw [show (RatFunc.X - 1) ^ dg *
        ((algebraMap ℚ (RatFunc ℚ)) (pp.coeff k) * (RatFunc.X ^ 2 / (RatFunc.X - 1)) ^ k)
      = (algebraMap ℚ (RatFunc ℚ)) (pp.coeff k)
        * ((RatFunc.X - 1) ^ dg * (RatFunc.X ^ 2 / (RatFunc.X - 1)) ^ k) by ring,
    hkey k hk']
  ring_nf

/-! ## The pointwise relation with polynomial coefficients -/

lemma lciz_rel {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) {pp : Fin 4 → Polynomial ℚ}
    {qq : Fin 3 → Polynomial ℚ} {J : Fin 3 → ℂ → ℂ} {dg : ℕ}
    (hdgk : ∀ k, (pp k).natDegree ≤ dg) (hdgi : ∀ i, (qq i).natDegree ≤ dg)
    {η : ℝ} (hη : 0 < η) (hηδ : η ≤ δ / 2)
    (hLC : ∀ z ∈ ball ninth δ,
      (∑ k : Fin 4, pAtY (pp k) z * DyIter k y9 z) + ∑ i : Fin 3, pAtY (qq i) z * J i z = 0) :
    ∀ z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2),
      (lcizA dg pp).eval₂ (algebraMap ℚ ℂ) z * y9 z
        + (lcizB dg pp).eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
        + ∑ i : Fin 3, (lcizC dg qq i).eval₂ (algebraMap ℚ ℂ) z * J i z = 0 := by
  intro z hz
  have hzB : z ∈ ball ninth δ := lciz_ball_sub hη hηδ hz
  have hz9 : z ≠ ninth := lciz_ne_ninth hη hz
  have hz1 : z ≠ 1 := lciz_ne_one hη hηδ hY.2.1 hz
  have hexp : (lcizA dg pp).eval₂ (algebraMap ℚ ℂ) z * y9 z
        + (lcizB dg pp).eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
        + ∑ i : Fin 3, (lcizC dg qq i).eval₂ (algebraMap ℚ ℂ) z * J i z
      = (∑ k : Fin 4, (Work.C17.clearedAtY (pp k) dg).eval₂ (algebraMap ℚ ℂ) z
            * (lcizE k).eval₂ (algebraMap ℚ ℂ) z * (AZpoly (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z) * y9 z
        + (∑ k : Fin 4, (Work.C17.clearedAtY (pp k) dg).eval₂ (algebraMap ℚ ℂ) z
            * (lcizE k).eval₂ (algebraMap ℚ ℂ) z * (BZpoly (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z)
          * deriv y9 z
        + ∑ i : Fin 3, ((Work.C17.clearedAtY (qq i) dg).eval₂ (algebraMap ℚ ℂ) z
            * (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z) * J i z := by
    simp only [lcizA, lcizB, lcizC, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Finset.sum_mul]
  rw [hexp]
  have htermA : ∀ k : Fin 4, (z - 1) ^ dg * (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z
        * (pAtY (pp k) z * DyIter k y9 z)
      = (Work.C17.clearedAtY (pp k) dg).eval₂ (algebraMap ℚ ℂ) z
          * (lcizE k).eval₂ (algebraMap ℚ ℂ) z * (AZpoly (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z * y9 z
        + (Work.C17.clearedAtY (pp k) dg).eval₂ (algebraMap ℚ ℂ) z
          * (lcizE k).eval₂ (algebraMap ℚ ℂ) z * (BZpoly (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z
            * deriv y9 z := by
    intro k
    have h1 := lciz_clearedAtY_eval (pp k) dg (hdgk k) hz1
    have h2 := chainZ_ana hY (k : ℕ) z hzB hz9
    have h3 : (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z
        = (lcizE k).eval₂ (algebraMap ℚ ℂ) z * (DZpoly (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z := by
      rw [← Polynomial.eval₂_mul, lcizE_mul]
    linear_combination (DyIter k y9 z * (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z) * h1
      + ((Work.C17.clearedAtY (pp k) dg).eval₂ (algebraMap ℚ ℂ) z * DyIter k y9 z) * h3
      + ((Work.C17.clearedAtY (pp k) dg).eval₂ (algebraMap ℚ ℂ) z
          * (lcizE k).eval₂ (algebraMap ℚ ℂ) z) * h2
  have htermJ : ∀ i : Fin 3, (z - 1) ^ dg * (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z
        * (pAtY (qq i) z * J i z)
      = ((Work.C17.clearedAtY (qq i) dg).eval₂ (algebraMap ℚ ℂ) z
          * (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z) * J i z := by
    intro i
    have h1 := lciz_clearedAtY_eval (qq i) dg (hdgi i) hz1
    linear_combination ((DZpoly 3).eval₂ (algebraMap ℚ ℂ) z * J i z) * h1
  have h0 : (z - 1) ^ dg * (DZpoly 3).eval₂ (algebraMap ℚ ℂ) z
      * ((∑ k : Fin 4, pAtY (pp k) z * DyIter k y9 z) + ∑ i : Fin 3, pAtY (qq i) z * J i z) = 0 := by
    rw [hLC z hzB, mul_zero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum] at h0
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => htermA k),
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => htermJ i)] at h0
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at h0
  simpa using h0

/-! ## Inverting the clearing -/

lemma lcizA_rat_zero {dg : ℕ} {pp : Fin 4 → Polynomial ℚ} (hd : ∀ k, (pp k).natDegree ≤ dg)
    (h : lcizA dg pp = 0) :
    (∑ k : Fin 4, (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs * (clsZ k).1) = 0 := by
  have hm : algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizA dg pp) = 0 := by rw [h, map_zero]
  rw [lcizA, map_sum] at hm
  have hfac : (∑ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (Work.C17.clearedAtY (pp k) dg * lcizE k * AZpoly (k : ℕ)))
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly 3)
        * (∑ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
            * (clsZ k).1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hcr : algebraMap (Polynomial ℚ) (RatFunc ℚ) (AZpoly (k : ℕ))
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ)) * (clsZ k).1 := by
      have := (chainZ_rat (k : ℕ)).1
      simpa only [clsZ] using this
    calc algebraMap (Polynomial ℚ) (RatFunc ℚ)
          (Work.C17.clearedAtY (pp k) dg * lcizE k * AZpoly (k : ℕ))
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k))
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (AZpoly (k : ℕ)) := by rw [map_mul, map_mul]
      _ = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k))
            * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ)) * (clsZ k).1) := by
          rw [hcr]
      _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly 3)
            * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
                * (clsZ k).1) := by
          rw [show (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
                * algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k))
                * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ)) * (clsZ k).1)
              = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
                * ((algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k)
                    * algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ))) * (clsZ k).1) by ring,
            ← map_mul, lcizE_mul]
          ring
  rw [hfac] at hm
  have hD3 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly 3) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (DZpoly_ne_zero 3)
  have hG1 : (∑ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
      * (clsZ k).1) = 0 := by
    rcases mul_eq_zero.mp hm with h' | h'
    · exact absurd h' hD3
    · exact h'
  have hbr : ∀ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
      = (RatFunc.X - 1) ^ dg * (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs :=
    fun k => lciz_clearedAtY_algebraMap (pp k) dg (hd k)
  have hG1' : (∑ k : Fin 4,
      ((RatFunc.X - 1) ^ dg * (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs) * (clsZ k).1) = 0 := by
    simpa only [hbr] using hG1
  have hfac2 : (RatFunc.X - 1 : RatFunc ℚ) ^ dg
      * (∑ k : Fin 4, (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs * (clsZ k).1) = 0 := by
    rw [Finset.mul_sum]
    simpa only [mul_assoc] using hG1'
  have hne : (RatFunc.X - 1 : RatFunc ℚ) ^ dg ≠ 0 := pow_ne_zero _ (by
    intro h0
    have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) = 0 := by
      rw [map_sub, map_one]; exact h0
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1) h1)
  exact (mul_eq_zero.mp hfac2).resolve_left hne

lemma lcizB_rat_zero {dg : ℕ} {pp : Fin 4 → Polynomial ℚ} (hd : ∀ k, (pp k).natDegree ≤ dg)
    (h : lcizB dg pp = 0) :
    (∑ k : Fin 4, (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs * (clsZ k).2) = 0 := by
  have hm : algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizB dg pp) = 0 := by rw [h, map_zero]
  rw [lcizB, map_sum] at hm
  have hfac : (∑ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (Work.C17.clearedAtY (pp k) dg * lcizE k * BZpoly (k : ℕ)))
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly 3)
        * (∑ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
            * (clsZ k).2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hcr : algebraMap (Polynomial ℚ) (RatFunc ℚ) (BZpoly (k : ℕ))
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ)) * (clsZ k).2 := by
      have := (chainZ_rat (k : ℕ)).2
      simpa only [clsZ] using this
    calc algebraMap (Polynomial ℚ) (RatFunc ℚ)
          (Work.C17.clearedAtY (pp k) dg * lcizE k * BZpoly (k : ℕ))
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k))
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (BZpoly (k : ℕ)) := by rw [map_mul, map_mul]
      _ = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k))
            * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ)) * (clsZ k).2) := by
          rw [hcr]
      _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly 3)
            * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
                * (clsZ k).2) := by
          rw [show (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
                * algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k))
                * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ)) * (clsZ k).2)
              = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
                * ((algebraMap (Polynomial ℚ) (RatFunc ℚ) (lcizE k)
                    * algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly (k : ℕ))) * (clsZ k).2) by ring,
            ← map_mul, lcizE_mul]
          ring
  rw [hfac] at hm
  have hD3 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly 3) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (DZpoly_ne_zero 3)
  have hG1 : (∑ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
      * (clsZ k).2) = 0 := by
    rcases mul_eq_zero.mp hm with h' | h'
    · exact absurd h' hD3
    · exact h'
  have hbr : ∀ k : Fin 4, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.clearedAtY (pp k) dg)
      = (RatFunc.X - 1) ^ dg * (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs :=
    fun k => lciz_clearedAtY_algebraMap (pp k) dg (hd k)
  have hG1' : (∑ k : Fin 4,
      ((RatFunc.X - 1) ^ dg * (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs) * (clsZ k).2) = 0 := by
    simpa only [hbr] using hG1
  have hfac2 : (RatFunc.X - 1 : RatFunc ℚ) ^ dg
      * (∑ k : Fin 4, (pp k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs * (clsZ k).2) = 0 := by
    rw [Finset.mul_sum]
    simpa only [mul_assoc] using hG1'
  have hne : (RatFunc.X - 1 : RatFunc ℚ) ^ dg ≠ 0 := pow_ne_zero _ (by
    intro h0
    have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) = 0 := by
      rw [map_sub, map_one]; exact h0
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1) h1)
  exact (mul_eq_zero.mp hfac2).resolve_left hne

/-! ## The main theorem -/

theorem lc_implies_zero {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) (p : Fin 4 → Polynomial ℚ)
    (q : Fin 3 → Polynomial ℚ) (J : Fin 3 → ℂ → ℂ)
    (hJd : ∀ i, DifferentiableOn ℂ (J i) (ball ninth δ)) (hJ0 : ∀ i, J i ninth = 0)
    (hJ' : ∀ i : Fin 3, ∀ z ∈ ball ninth δ,
      HasDerivAt (J i) ((yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z) z)
    (hLC : ∀ z ∈ ball ninth δ,
      (∑ k : Fin 4, pAtY (p k) z * DyIter k y9 z)
        + ∑ i : Fin 3, pAtY (q i) z * J i z = 0) :
    p = 0 ∧ q = 0 := by
  obtain ⟨hδpos, hδle, hy9d, hy9ne9, hode9⟩ := hY
  have hY' : Y9 y9 δ := ⟨hδpos, hδle, hy9d, hy9ne9, hode9⟩
  -- `y9` is nonzero on a neighbourhood of `1/9`
  have hy9At : DifferentiableAt ℂ y9 ninth :=
    hy9d.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp (hy9At.continuousAt.eventually_ne hy9ne9)
  set η : ℝ := min ε (δ / 2) with hηdef
  have hηpos : 0 < η := lt_min hεpos (by linarith)
  have hηδ : η ≤ δ / 2 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  have hy9c : y9 (((1 / 9 + η / 2 : ℝ) : ℂ)) ≠ 0 := by
    refine hε ?_
    rw [Complex.dist_eq, lciz_ninth_cast]
    have hcast : ((1 / 9 + η / 2 : ℝ) : ℂ) - ((1 / 9 : ℝ) : ℂ) = ((η / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, show ‖((η / 2 : ℝ) : ℂ)‖ = |η / 2| from RCLike.norm_ofReal (η / 2),
      abs_of_pos (by linarith : (0 : ℝ) < η / 2)]
    linarith
  -- the cleared coefficient data
  set dg : ℕ := max ((Finset.univ : Finset (Fin 4)).sup fun k => (p k).natDegree)
      ((Finset.univ : Finset (Fin 3)).sup fun i => (q i).natDegree) with hdgdef
  have hdgk : ∀ k : Fin 4, (p k).natDegree ≤ dg := fun k => by
    rw [hdgdef]
    exact le_trans (Finset.le_sup (f := fun j : Fin 4 => (p j).natDegree) (Finset.mem_univ k))
      (le_max_left _ _)
  have hdgi : ∀ i : Fin 3, (q i).natDegree ≤ dg := fun i => by
    rw [hdgdef]
    exact le_trans (Finset.le_sup (f := fun j : Fin 3 => (q j).natDegree) (Finset.mem_univ i))
      (le_max_right _ _)
  -- the pointwise relation
  have hrel : ∀ z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2),
      ((lcizA dg p).map (algebraMap ℚ ℂ)).eval z * y9 z
        + ((lcizB dg p).map (algebraMap ℚ ℂ)).eval z * deriv y9 z
        + ∑ i : Fin 3, ((lcizC dg q i).map (algebraMap ℚ ℂ)).eval z * J i z = 0 := by
    intro z hz
    have := lciz_rel hY' hdgk hdgi hηpos hηδ hLC z hz
    simpa only [Polynomial.eval₂_eq_eval_map] using this
  -- the ODE in polynomial form
  have hode' : ∀ z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2),
      (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).eval z * deriv (deriv y9) z
        + (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ).eval z * deriv y9 z
        + (-3 + 9 * X : Polynomial ℂ).eval z * y9 z = 0 := by
    intro z hz
    have h := hode9 z (lciz_ball_sub hηpos hηδ hz)
    rw [LZ] at h
    have e1 : (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).eval z = PZ z := by
      simp only [PZ, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      ring
    have e2 : (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ).eval z = PZ' z := by
      simp only [PZ', Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    have e3 : (-3 + 9 * X : Polynomial ℂ).eval z = RZ z := by
      simp only [RZ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_ofNat]
      ring
    rw [e1, e2, e3]
    exact h
  have hp2 : (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ) ≠ 0 := by
    intro h
    have h3 := congrArg (fun r : Polynomial ℂ => r.eval 2) h
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_zero] at h3
    norm_num at h3
  have hp2ne : ∀ z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2),
      (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).eval z ≠ 0 := by
    intro z hz
    have e1 : (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).eval z = PZ z := by
      simp only [PZ, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      ring
    rw [e1]
    exact PZ_ne_zero_of_mem_ball_ninth hδle (lciz_ball_sub hηpos hηδ hz) (lciz_ne_ninth hηpos hz)
  have hrd : ∀ i : Fin 3, rdC i ≠ 0 := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · rw [show rdC (0 : Fin 3) = (X - 1) ^ 2 by rfl]
      exact pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero 1)
    · rw [show rdC (1 : Fin 3) = X * (X - 1) by rfl]
      exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero 1)
    · rw [show rdC (2 : Fin 3) = X ^ 3 by rfl]
      exact pow_ne_zero 3 Polynomial.X_ne_zero
  have hrdne : ∀ i : Fin 3, ∀ z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2),
      (rdC i).eval z ≠ 0 := by
    intro i z hz
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    have hz0 : z ≠ 0 := lciz_ne_zero hηpos hz
    have hz1 : z ≠ 1 := lciz_ne_one hηpos hηδ hδle hz
    rcases hi with rfl | rfl | rfl
    · rw [show rdC (0 : Fin 3) = (X - 1) ^ 2 by rfl]
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
      exact pow_ne_zero 2 (sub_ne_zero.mpr hz1)
    · rw [show rdC (1 : Fin 3) = X * (X - 1) by rfl]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
      exact mul_ne_zero hz0 (sub_ne_zero.mpr hz1)
    · rw [show rdC (2 : Fin 3) = X ^ 3 by rfl]
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero 3 hz0
  have hJd' : ∀ i : Fin 3, DifferentiableOn ℂ (J i) (ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2)) :=
    fun i => (hJd i).mono (fun z hz => lciz_ball_sub hηpos hηδ hz)
  have hJderiv' : ∀ i : Fin 3, ∀ z ∈ ball (((1 / 9 + η / 2 : ℝ) : ℂ)) (η / 2),
      HasDerivAt (J i) ((rnC i).eval z / (rdC i).eval z * y9 z) z := by
    intro i z hz
    have hz0 : z ≠ 0 := lciz_ne_zero hηpos hz
    have hz1 : z ≠ 1 := lciz_ne_one hηpos hηδ hδle hz
    have h := hJ' i z (lciz_ball_sub hηpos hηδ hz)
    rw [lciz_deriv_coeff i hz0 hz1] at h
    exact h
  have hadj' : ∀ (β : RatFunc ℂ) (c : Fin 3 → ℂ),
      Submission.CDT.dRat (Submission.CDT.dRat
          ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 10 * X ^ 2 + 9 * X ^ 3)) * β))
        - Submission.CDT.dRat
            ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - 20 * X + 27 * X ^ 2)) * β)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (-3 + 9 * X)) * β
        = ∑ i : Fin 3, (algebraMap ℂ (RatFunc ℂ) (c i))
            * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rnC i)
                / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rdC i)) →
      β = 0 ∧ c = 0 := by
    intro β c h
    refine adjointZ_no_solution β c ?_
    have h' : (∑ i : Fin 3, (algebraMap ℂ (RatFunc ℂ) (c i))
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rnC i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rdC i)))
        = ∑ i : Fin 3, (algebraMap ℂ (RatFunc ℂ) (c i)) * rQc i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lciz_rQc_eq i]
    rwa [h'] at h
  obtain ⟨hA0, hB0, hC0⟩ := Work.GenShared.periods_indep_gen (k := 3)
    (p2 := (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ))
    (p1 := (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ))
    (p0 := (-3 + 9 * X : Polynomial ℂ))
    hp2 rnC rdC hrd (fun u => riccatiZ_no_rational u) hadj'
    (((1 / 9 + η / 2 : ℝ) : ℂ)) (by linarith) hp2ne hrdne
    y9 (hy9d.mono (fun z hz => lciz_ball_sub hηpos hηδ hz))
    ⟨(((1 / 9 + η / 2 : ℝ) : ℂ)), Metric.mem_ball_self (by linarith), hy9c⟩
    hode' J hJd' hJderiv'
    ((lcizA dg p).map (algebraMap ℚ ℂ)) ((lcizB dg p).map (algebraMap ℚ ℂ))
    (fun i => (lcizC dg q i).map (algebraMap ℚ ℂ)) hrel
  have hAzero : lcizA dg p = 0 :=
    (Polynomial.map_eq_zero_iff Rat.cast_injective).mp hA0
  have hBzero : lcizB dg p = 0 :=
    (Polynomial.map_eq_zero_iff Rat.cast_injective).mp hB0
  constructor
  · refine classZ_injective p ⟨lcizA_rat_zero hdgk hAzero, lcizB_rat_zero hdgk hBzero⟩
  · funext i
    have hCi : lcizC dg q i = 0 := by
      have hmap : (lcizC dg q i).map (algebraMap ℚ ℂ) = 0 := by
        have := congrFun hC0 i
        simpa only [Pi.zero_apply] using this
      exact (Polynomial.map_eq_zero_iff Rat.cast_injective).mp hmap
    have hcl : Work.C17.clearedAtY (q i) dg = 0 := by
      have h := hCi
      simp only [lcizC] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (DZpoly_ne_zero 3)
    exact (lciz_clearedAtY_eq_zero_iff (q i) dg (hdgi i)).mp hcl

end Work.A14D
