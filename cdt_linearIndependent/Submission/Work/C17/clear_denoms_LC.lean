import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.exists_cleared_pAtY
import Submission.Work.C17.DyIter_eq_cls

namespace Work.C17

open Polynomial
open scoped BigOperators

noncomputable section

/-!
# Clearing the denominators in the `(LC)` identity (area C17)

`Work.C17.clear_denoms_LC` takes the identity `(LC)` produced by `Work.C17.relation_to_LC`
(a relation `Σ_k p_k(y)·D_y^k y₁ + Σ_i q_i(y)·J_{jrev i} = 0` on the disc) and clears the
denominator `(z-1)^d` of the rational functions `z ↦ p(y(z))` (`y(z) = z²/(z-1)`), using the
denominator-cleared form of the ODE for `y₁` supplied by `Work.C17.DyIter_eq_cls`.

The resulting relation `A₀·y₁ + B₀·y₁' + Σ_i C_i·J_i = 0` is *lossless*: if `A₀ = 0` then the
`y₁`-part of the original `(LC)` relation already vanishes in `ℚ(x)`, and likewise for `B₀`;
and `C_{jrev i} = 0` forces `q_i = 0`.

## The clearing identities used

* `algebraMap_clearedAtY` : in `ℚ(x)`, `(x-1)^d · p(y) = clearedAtY p d` (`y = x²/(x-1)`);
* `clearedAtY_eval₂` : pointwise, `(z-1)^d · pAtY p z = (clearedAtY p d)(z)` for `z ≠ 1`.

The disc `ball(x_s, δ)` never meets `z = 1` (it lies in `|z| < 1`), so the second identity is
available at every point of the disc, and the first one makes the clearing invertible in `ℚ(x)`.
-/

/-! ## Elementary facts about `ℚ(x) = RatFunc ℚ` -/

/-- The structure map `ℚ[X] → ℚ(x)` is injective (`ℚ[X]` is a domain). -/
lemma algebraMap_poly_ratfunc_injective :
    Function.Injective (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
  intro p q h
  apply IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ))
  apply RatFunc.ofFractionRing_injective
  rw [RatFunc.ofFractionRing_algebraMap, RatFunc.ofFractionRing_algebraMap]
  exact h

/-- `X` maps to `xQ` under `ℚ[X] → ℚ(x)`. -/
lemma algebraMap_poly_X : algebraMap (Polynomial ℚ) (RatFunc ℚ) (X : Polynomial ℚ) = xQ := by
  rw [RatFunc.algebraMap_X]; rfl

/-- `xQ ≠ 1` in `ℚ(x)`. -/
lemma xQ_ne_one : (xQ : RatFunc ℚ) ≠ 1 := by
  intro h1
  have h2 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (X : Polynomial ℚ)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (1 : Polynomial ℚ) := by
    rw [algebraMap_poly_X, map_one]; exact h1
  have h3 := algebraMap_poly_ratfunc_injective h2
  exact Polynomial.X_ne_C (1 : ℚ) (by simpa [Polynomial.C_1] using h3)

/-- `xQ - 1 ≠ 0` in `ℚ(x)`. -/
lemma xQ_sub_one_ne_zero : (xQ - 1 : RatFunc ℚ) ≠ 0 := sub_ne_zero.mpr xQ_ne_one

/-- `(z-1)^d · y^k = z^{2k}·(z-1)^{d-k}` for `k ≤ d`, i.e. the clearing of `y^k`. -/
lemma yQ_pow_mul (k d : ℕ) (hk : k ≤ d) :
    (xQ - 1)^d * yQ^k = xQ^(2*k) * (xQ - 1)^(d-k) := by
  have hx := xQ_sub_one_ne_zero
  rw [show yQ^k = xQ^(2*k) / (xQ - 1)^k by rw [yQ, div_pow, ← pow_mul],
    ← mul_div_assoc, div_eq_iff (pow_ne_zero k hx)]
  rw [show xQ ^ (2 * k) * (xQ - 1) ^ (d - k) * (xQ - 1) ^ k
        = xQ ^ (2*k) * ((xQ - 1) ^ (d - k) * (xQ - 1) ^ k) by ring,
      ← pow_add, Nat.sub_add_cancel hk]
  ring

/-- Constants of `ℚ[X]` map to constants of `ℚ(x)`. -/
lemma algebraMap_poly_C (c : ℚ) :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (C c) = algebraMap ℚ (RatFunc ℚ) c := by
  rw [Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ)]

/-- A non-zero polynomial is non-zero in `ℚ(x)`. -/
lemma algebraMap_ne_zero {D : Polynomial ℚ} (hD : D ≠ 0) :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) D ≠ 0 :=
  fun h => hD (algebraMap_poly_ratfunc_injective (by rw [h, map_zero]))

/-- **The clearing identity in `ℚ(x)`**: `(x-1)^d · p(y) = clearedAtY p d` for `d ≥ p.natDegree`. -/
lemma algebraMap_clearedAtY (p : Polynomial ℚ) (d : ℕ) (hd : p.natDegree ≤ d) :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (clearedAtY p d)
      = (xQ - 1) ^ d * p.eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ := by
  rw [clearedAtY, map_sum]
  rw [Polynomial.eval₂_eq_sum_range' (algebraMap ℚ (RatFunc ℚ)) (S := RatFunc ℚ)
    (n := d+1) (by omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp hk
  simp only [map_mul, map_pow, map_sub, map_one, algebraMap_poly_X]
  rw [algebraMap_poly_C]
  rw [show algebraMap ℚ (RatFunc ℚ) (p.coeff k) * xQ ^ (2 * k) * (xQ - 1) ^ (d - k)
      = algebraMap ℚ (RatFunc ℚ) (p.coeff k) * (xQ ^ (2 * k) * (xQ - 1) ^ (d - k)) by ring]
  rw [← yQ_pow_mul k d hk']
  ring

/-! ## The clearing identity at the level of functions -/

/-- Pointwise clearing: `(z-1)^d · pAtY p z = (clearedAtY p d)(z)` for `z ≠ 1` and
`d ≥ p.natDegree` (the content of `exists_cleared_pAtY`, with the witness made explicit). -/
lemma clearedAtY_eval₂ (p : Polynomial ℚ) (d : ℕ) (hd : p.natDegree ≤ d) (z : ℂ)
    (hz : z ≠ 1) : (z - 1) ^ d * pAtY p z = (clearedAtY p d).eval₂ (algebraMap ℚ ℂ) z := by
  have hpow : ∀ k ≤ d, (z - 1) ^ d * yC z ^ k = z ^ (2 * k) * (z - 1) ^ (d - k) := by
    intro k hk
    have h1 : (z - 1) * yC z = z ^ 2 := by rw [yC]; field_simp
    calc (z - 1) ^ d * yC z ^ k
        = ((z - 1) ^ (d - k) * (z - 1) ^ k) * yC z ^ k := by
            rw [← pow_add, Nat.sub_add_cancel hk]
      _ = (z - 1) ^ (d - k) * ((z - 1) ^ k * yC z ^ k) := by ring
      _ = (z - 1) ^ (d - k) * ((z - 1) * yC z) ^ k := by rw [mul_pow]
      _ = (z - 1) ^ (d - k) * (z ^ 2) ^ k := by rw [h1]
      _ = z ^ (2 * k) * (z - 1) ^ (d - k) := by rw [pow_mul]; ring
  have hp1 : pAtY p z
      = ∑ k ∈ Finset.range (d + 1), (algebraMap ℚ ℂ (p.coeff k)) * yC z ^ k := by
    rw [pAtY, Polynomial.eval₂_eq_sum_range' (algebraMap ℚ ℂ) (n := d + 1) (by omega)]
  rw [hp1, Finset.mul_sum]
  simp only [clearedAtY, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_one]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp hk
  rw [show (z - 1) ^ d * ((algebraMap ℚ ℂ) (p.coeff k) * yC z ^ k)
        = (algebraMap ℚ ℂ) (p.coeff k) * ((z - 1) ^ d * yC z ^ k) by ring]
  rw [hpow k hk']
  ring

/-- The clearing is lossless: `clearedAtY p d = 0 ↔ p = 0` when `d ≥ p.natDegree`. -/
lemma clearedAtY_eq_zero_iff (p : Polynomial ℚ) (d : ℕ) (hd : p.natDegree ≤ d) :
    clearedAtY p d = 0 ↔ p = 0 := by
  refine ⟨?_, ?_⟩
  · intro hA
    by_contra hp
    have hcoe := coeff_clearedAtY p d hd
    rw [hA, Polynomial.coeff_zero] at hcoe
    have hz : p.leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree]; exact hcoe.symm
    exact hp (Polynomial.leadingCoeff_eq_zero.mp hz)
  · intro hp
    rw [hp]; simp [clearedAtY]

/-! ## The main lemma -/

theorem clear_denoms_LC (a b : ℚ) {δ : ℝ} (hδ : 0 < δ)
    (hxs : 0 < Work.C17.xs a b) (hδb : 2 * δ ≤ 1 - Work.C17.xs a b)
    (y1 : ℂ → ℂ) (J : Fin 6 → ℂ → ℂ)
    (D : Polynomial ℚ) (hD : D ≠ 0)
    (A B : Fin 4 → Polynomial ℚ)
    (hAB : ∀ k : Fin 4,
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) (A k)
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) D * (Work.C17.cls a b k).1 ∧
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (B k)
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) D * (Work.C17.cls a b k).2) ∧
      (∀ z ∈ Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ,
        (D.eval₂ (algebraMap ℚ ℂ) z) * Work.C17.DyIter (k : ℕ) y1 z
          = (A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
            + (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z))
    (p : Fin 4 → Polynomial ℚ) (q : Fin 6 → Polynomial ℚ)
    (hL : ∀ z ∈ Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ,
      (∑ k : Fin 4, Work.C17.pAtY (p k) z * Work.C17.DyIter (k : ℕ) y1 z)
        + (∑ i : Fin 6, Work.C17.pAtY (q i) z * J (Work.C17.jrev i) z) = 0) :
    ∃ A0 B0 : Polynomial ℚ, ∃ C : Fin 6 → Polynomial ℚ,
      (∀ z ∈ Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ,
        (A0.eval₂ (algebraMap ℚ ℂ) z) * y1 z + (B0.eval₂ (algebraMap ℚ ℂ) z) * deriv y1 z
          + (∑ i : Fin 6, (C i).eval₂ (algebraMap ℚ ℂ) z * J i z) = 0) ∧
      (A0 = 0 → (∑ k : Fin 4,
          ((p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) Work.C17.yQ) * (Work.C17.cls a b k).1) = 0) ∧
      (B0 = 0 → (∑ k : Fin 4,
          ((p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) Work.C17.yQ) * (Work.C17.cls a b k).2) = 0) ∧
      (∀ i : Fin 6, C (Work.C17.jrev i) = 0 → q i = 0) := by
  -- a common degree bound `d` for all the numerator polynomials
  obtain ⟨d, hpd, hqd⟩ : ∃ d : ℕ,
      (∀ k : Fin 4, (p k).natDegree ≤ d) ∧ (∀ i : Fin 6, (q i).natDegree ≤ d) := by
    refine ⟨(∑ k : Fin 4, (p k).natDegree) + (∑ i : Fin 6, (q i).natDegree), ?_, ?_⟩
    · intro k
      have h := Finset.single_le_sum (f := fun k : Fin 4 => (p k).natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    · intro i
      have h := Finset.single_le_sum (f := fun i : Fin 6 => (q i).natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
  -- the disc avoids `z = 1`
  have hxs1 : Work.C17.xs a b < 1 := by
    have : (0:ℝ) < 2 * δ := by linarith
    linarith
  refine ⟨∑ k : Fin 4, clearedAtY (p k) d * A k, ∑ k : Fin 4, clearedAtY (p k) d * B k,
    fun i : Fin 6 => D * clearedAtY (q (jrev i)) d, ?_, ?_, ?_, ?_⟩
  · -- the pointwise identity on the disc
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [Metric.mem_ball, h] at hz
      have heq : dist (1 : ℂ) (((Work.C17.xs a b : ℝ)) : ℂ) = |1 - Work.C17.xs a b| := by
        rw [dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
      rw [heq, abs_of_pos (by linarith)] at hz
      linarith
    have hcl : ∀ k : Fin 4, (z - 1) ^ d * pAtY (p k) z
        = (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z :=
      fun k => clearedAtY_eval₂ (p k) d (hpd k) z hz1
    have hclq : ∀ i : Fin 6, (z - 1) ^ d * pAtY (q i) z
        = (clearedAtY (q i) d).eval₂ (algebraMap ℚ ℂ) z :=
      fun i => clearedAtY_eval₂ (q i) d (hqd i) z hz1
    have hDk : ∀ k : Fin 4, (D.eval₂ (algebraMap ℚ ℂ) z) * DyIter (k : ℕ) y1 z
        = (A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
          + (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z :=
      fun k => (hAB k).2 z hz
    -- multiply the relation by `(z-1)^d · D(z)` and clear
    have key : (∑ k : Fin 4, (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
          * ((A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
              + (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z))
        + (∑ i : Fin 6, (D.eval₂ (algebraMap ℚ ℂ) z
            * (clearedAtY (q i) d).eval₂ (algebraMap ℚ ℂ) z) * J (jrev i) z) = 0 := by
      have hm : ((z - 1) ^ d * D.eval₂ (algebraMap ℚ ℂ) z) *
          ((∑ k : Fin 4, pAtY (p k) z * DyIter (k : ℕ) y1 z)
            + (∑ i : Fin 6, pAtY (q i) z * J (jrev i) z)) = 0 := by
        rw [hL z hz, mul_zero]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum] at hm
      have hk_eq : ∀ k : Fin 4, ((z - 1) ^ d * D.eval₂ (algebraMap ℚ ℂ) z)
            * (pAtY (p k) z * DyIter (k : ℕ) y1 z)
          = (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
            * ((A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
                + (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z) := by
        intro k
        calc ((z - 1) ^ d * D.eval₂ (algebraMap ℚ ℂ) z)
              * (pAtY (p k) z * DyIter (k : ℕ) y1 z)
            = ((z - 1) ^ d * pAtY (p k) z)
              * (D.eval₂ (algebraMap ℚ ℂ) z * DyIter (k : ℕ) y1 z) := by ring
          _ = (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
              * ((A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
                  + (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z) := by
              rw [hcl k, hDk k]
      have hi_eq : ∀ i : Fin 6, ((z - 1) ^ d * D.eval₂ (algebraMap ℚ ℂ) z)
            * (pAtY (q i) z * J (jrev i) z)
          = (D.eval₂ (algebraMap ℚ ℂ) z
              * (clearedAtY (q i) d).eval₂ (algebraMap ℚ ℂ) z) * J (jrev i) z := by
        intro i
        calc ((z - 1) ^ d * D.eval₂ (algebraMap ℚ ℂ) z) * (pAtY (q i) z * J (jrev i) z)
            = (D.eval₂ (algebraMap ℚ ℂ) z * ((z - 1) ^ d * pAtY (q i) z))
                * J (jrev i) z := by ring
          _ = (D.eval₂ (algebraMap ℚ ℂ) z
              * (clearedAtY (q i) d).eval₂ (algebraMap ℚ ℂ) z) * J (jrev i) z := by rw [hclq i]
      rw [Finset.sum_congr rfl (fun k _ => hk_eq k),
        Finset.sum_congr rfl (fun i _ => hi_eq i)] at hm
      exact hm
    -- identify the sums with the `A₀`, `B₀`, `C` used in the statement
    have hsplit : (∑ k : Fin 4, (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
          * ((A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
              + (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z))
        = (∑ k : Fin 4, (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
              * (A k).eval₂ (algebraMap ℚ ℂ) z * y1 z)
          + (∑ k : Fin 4, (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
              * (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hA0 : (∑ k : Fin 4, clearedAtY (p k) d * A k).eval₂ (algebraMap ℚ ℂ) z * y1 z
        = ∑ k : Fin 4, (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
            * (A k).eval₂ (algebraMap ℚ ℂ) z * y1 z := by
      rw [Polynomial.eval₂_finsetSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.eval₂_mul]
    have hB0 : (∑ k : Fin 4, clearedAtY (p k) d * B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        = ∑ k : Fin 4, (clearedAtY (p k) d).eval₂ (algebraMap ℚ ℂ) z
            * (B k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z := by
      rw [Polynomial.eval₂_finsetSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.eval₂_mul]
    have hCsum : (∑ i : Fin 6, (D * clearedAtY (q (jrev i)) d).eval₂ (algebraMap ℚ ℂ) z * J i z)
        = ∑ i : Fin 6, (D.eval₂ (algebraMap ℚ ℂ) z
            * (clearedAtY (q (jrev i)) d).eval₂ (algebraMap ℚ ℂ) z) * J i z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.eval₂_mul]
    have hjrev : (∑ i : Fin 6, (D.eval₂ (algebraMap ℚ ℂ) z
            * (clearedAtY (q i) d).eval₂ (algebraMap ℚ ℂ) z) * J (jrev i) z)
        = ∑ i : Fin 6, (D.eval₂ (algebraMap ℚ ℂ) z
            * (clearedAtY (q (jrev i)) d).eval₂ (algebraMap ℚ ℂ) z) * J i z :=
      sum_jrev _ _ (fun i => by rw [jrev_invol])
    rw [hsplit] at key
    rw [hA0, hB0, hCsum, ← hjrev]
    exact key
  · -- `A₀ = 0` loses no information on the `y₁`-part
    intro hA0
    have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (∑ k : Fin 4, clearedAtY (p k) d * A k) = 0 := by rw [hA0, map_zero]
    rw [map_sum] at h1
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [map_mul, algebraMap_clearedAtY (p k) d (hpd k), (hAB k).1.1])] at h1
    have h2 : (∑ k : Fin 4, ((xQ - 1) ^ d * (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ)
          * (algebraMap (Polynomial ℚ) (RatFunc ℚ) D * (cls a b k).1))
        = (xQ - 1) ^ d * algebraMap (Polynomial ℚ) (RatFunc ℚ) D
          * (∑ k : Fin 4, (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ * (cls a b k).1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (pow_ne_zero _ xQ_sub_one_ne_zero)
      (algebraMap_ne_zero hD))
  · -- `B₀ = 0` likewise
    intro hB0
    have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (∑ k : Fin 4, clearedAtY (p k) d * B k) = 0 := by rw [hB0, map_zero]
    rw [map_sum] at h1
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [map_mul, algebraMap_clearedAtY (p k) d (hpd k), (hAB k).1.2])] at h1
    have h2 : (∑ k : Fin 4, ((xQ - 1) ^ d * (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ)
          * (algebraMap (Polynomial ℚ) (RatFunc ℚ) D * (cls a b k).2))
        = (xQ - 1) ^ d * algebraMap (Polynomial ℚ) (RatFunc ℚ) D
          * (∑ k : Fin 4, (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ * (cls a b k).2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (pow_ne_zero _ xQ_sub_one_ne_zero)
      (algebraMap_ne_zero hD))
  · -- the clearing of the `q`-part is lossless
    intro i hC
    have h1 : D * clearedAtY (q i) d = 0 := by
      have h := hC
      simpa only [jrev_invol] using h
    have h2 : clearedAtY (q i) d = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hD
      · exact h
    exact (clearedAtY_eq_zero_iff (q i) d (hqd i)).1 h2

end

end Work.C17
