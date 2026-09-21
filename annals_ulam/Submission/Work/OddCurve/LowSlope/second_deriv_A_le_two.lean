import Mathlib

/-!
# The estimate `(1 + r·(2n+2)/(2n+1))·R²/(R^(2n+2)·(R+r)) ≤ 2`

The statement is a purely numerical inequality about the radial pair `(R, r)` of the `(2n+1)`-dimensional
system, restricted to the "low slope" box.  Write `k = 2n+2`, `K = k-1 = 2n+1`, so that the hypotheses are
`R^k ≥ 3/8`, `R^k + r^k ≥ 3/2` and `|R^K - r^K| ≤ 1/2`.  The proof only uses those three (the upper box
bounds `R^k ≤ 15/8` etc. are not needed).

## Structure

1. From `R^k + r^k ≥ 3/2` and `r^K ≤ R^K + 1/2` (the chord hypothesis) one gets the *balance* inequality
   `R^K (R + r) ≥ (3 - r)/2`.
2. Dividing, the target is equivalent to `E ≥ 0` with
   `E = 2 R^(K-1) (R+r) - 1 - r (K+1)/K`, and step 1 gives `E ≥ (3 - F)/R` where `F = R + r + R r (K+1)/K`.
3. **Case I** `2 R^(K-1) ≥ (K+1)/K`: then `E ≥ 2 R^K - 1 ≥ 0`, because `R^(K-1) ≥ (K+1)/(2K)` forces
   `R ≥ K/(K+1)` (via `(1 - 1/m)^m ≤ e^{-1} < 3/8`) and hence `R^K ≥ 1/2`.
4. **Case II** `2 R^(K-1) < (K+1)/K`: put `c = (K+1)/(2K)` and `U = 1 - 1/(2K)`.  Then `R^(K-1) < c ≤ U^(K-1)`
   (Bernoulli), so `R < U`; the chord hypothesis plus Bernoulli give `r ≤ 1 + (R^K - 1/2)/K`.  Expanding and
   bounding `R^K < cR`, `R^(K+1) < cR²`, `R ≤ U` yields
   `F ≤ U + (1 + (K+1)/K) U + ((K+1)²/(2K³)) U² = 3 - (3K² + 2K - 1)/(8K⁵) ≤ 3`,
   so `E ≥ (3 - F)/R ≥ 0`.
-/

set_option maxHeartbeats 800000

namespace Work.OddCurve.LowSlope

/-- `Real.exp (-1) < 3/8` (since `8/3 < e`). -/
private lemma exp_neg_one_lt_three_eighths : Real.exp (-1) < (3 : ℝ) / 8 := by
  rw [Real.exp_neg, inv_eq_one_div]
  have h : (1 : ℝ) / Real.exp 1 < (1 : ℝ) / (8 / 3) :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have h2 : (1 : ℝ) / (8 / 3) = 3 / 8 := by norm_num
  linarith

/-- Bernoulli step: `(K+1)/(2K) ≤ (1 - 1/(2K))^(K-1)`. -/
private lemma bern_U (K : ℕ) (hK : 1 ≤ K) :
    ((K : ℝ) + 1) / (2 * (K : ℝ)) ≤ (1 - 1 / (2 * (K : ℝ))) ^ (K - 1) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show (0 : ℕ) < K by omega)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have ha : (-2 : ℝ) ≤ -(1 / (2 * (K : ℝ))) := by
    rw [neg_le_neg_iff, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (K : ℝ))]
    linarith
  have h := one_add_mul_le_pow (a := -(1 / (2 * (K : ℝ)))) ha (K - 1)
  have hcast : 1 + ((K - 1 : ℕ) : ℝ) * (-(1 / (2 * (K : ℝ))))
      = ((K : ℝ) + 1) / (2 * (K : ℝ)) := by
    rw [Nat.cast_sub hK]; push_cast; field_simp; ring
  rw [hcast] at h
  simpa [sub_eq_add_neg] using h

/-- From `r^K ≤ R^K + 1/2` deduce `r ≤ 1 + (R^K - 1/2)/K` (`K ≥ 1`). -/
private lemma rt_bound (K : ℕ) (hK : 1 ≤ K) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrub : r ^ K ≤ R ^ K + 1 / 2) : r ≤ 1 + (R ^ K - 1 / 2) / (K : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show (0 : ℕ) < K by omega)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hRKnn : (0 : ℝ) ≤ R ^ K := by positivity
  set rt : ℝ := 1 + (R ^ K - 1 / 2) / (K : ℝ) with hrt
  have hrt0 : 0 ≤ rt := by
    rw [hrt]
    have h1 : -(1 / 2) / (K : ℝ) ≤ (R ^ K - 1 / 2) / (K : ℝ) := by
      rw [div_le_div_iff_of_pos_right hKpos]; linarith
    have h2 : (-1 : ℝ) ≤ -(1 / 2) / (K : ℝ) := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ hKpos]; linarith
    linarith
  have ha : (-2 : ℝ) ≤ (R ^ K - 1 / 2) / (K : ℝ) := by
    have h1 : -(1 / 2) / (K : ℝ) ≤ (R ^ K - 1 / 2) / (K : ℝ) := by
      rw [div_le_div_iff_of_pos_right hKpos]; linarith
    have h2 : (-2 : ℝ) ≤ -(1 / 2) / (K : ℝ) := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ hKpos]; linarith
    linarith
  have h := one_add_mul_le_pow (a := (R ^ K - 1 / 2) / (K : ℝ)) ha K
  have hcast : 1 + (K : ℝ) * ((R ^ K - 1 / 2) / (K : ℝ)) = R ^ K + 1 / 2 := by
    field_simp; ring
  rw [hcast, ← hrt] at h
  exact (pow_le_pow_iff_left₀ hr.le hrt0 (by omega)).mp (le_trans hrub h)

/-- Expansion of the bound `R + (1 + (R^K-1/2)/K)(1 + R(K+1)/K)`. -/
private lemma expand_F (K : ℕ) (hK : 1 ≤ K) (R : ℝ) :
    R + (1 + (R ^ K - 1 / 2) / (K : ℝ)) * (1 + R * (((K : ℝ) + 1) / (K : ℝ)))
      = (1 - 1 / (2 * (K : ℝ)))
        + (1 + ((K : ℝ) + 1) / (K : ℝ) - ((K : ℝ) + 1) / (2 * (K : ℝ) ^ 2)) * R
        + (1 / (K : ℝ)) * R ^ K + (((K : ℝ) + 1) / (K : ℝ) ^ 2) * R ^ (K + 1) := by
  have hKne : (K : ℝ) ≠ 0 := by
    have : (0 : ℕ) < K := by omega
    exact_mod_cast (ne_of_gt this)
  field_simp
  ring

/-- Combination of the substituted terms. -/
private lemma combine_F (K : ℕ) (hK : 1 ≤ K) (R : ℝ) :
    (1 - 1 / (2 * (K : ℝ)))
        + (1 + ((K : ℝ) + 1) / (K : ℝ) - ((K : ℝ) + 1) / (2 * (K : ℝ) ^ 2)) * R
        + (1 / (K : ℝ)) * (((K : ℝ) + 1) / (2 * (K : ℝ)) * R)
        + (((K : ℝ) + 1) / (K : ℝ) ^ 2) * (((K : ℝ) + 1) / (2 * (K : ℝ)) * R ^ 2)
      = (1 - 1 / (2 * (K : ℝ))) + (1 + ((K : ℝ) + 1) / (K : ℝ)) * R
        + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * R ^ 2 := by
  have hKne : (K : ℝ) ≠ 0 := by
    have : (0 : ℕ) < K := by omega
    exact_mod_cast (ne_of_gt this)
  field_simp
  ring

/-- The final numerical bound at `U = 1 - 1/(2K)`. -/
private lemma final_bound (K : ℕ) (hK : 1 ≤ K) :
    (1 - 1 / (2 * (K : ℝ))) + (1 + ((K : ℝ) + 1) / (K : ℝ)) * (1 - 1 / (2 * (K : ℝ)))
        + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * (1 - 1 / (2 * (K : ℝ))) ^ 2 ≤ 3 := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show (0 : ℕ) < K by omega)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hident : (1 - 1 / (2 * (K : ℝ)))
        + (1 + ((K : ℝ) + 1) / (K : ℝ)) * (1 - 1 / (2 * (K : ℝ)))
        + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * (1 - 1 / (2 * (K : ℝ))) ^ 2
      = 3 - (3 * (K : ℝ) ^ 2 + 2 * (K : ℝ) - 1) / (8 * (K : ℝ) ^ 5) := by
    have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
    field_simp
    ring
  rw [hident]
  have hnum : (0 : ℝ) < 3 * (K : ℝ) ^ 2 + 2 * (K : ℝ) - 1 := by
    nlinarith [hK1, sq_nonneg ((K : ℝ) - 1)]
  have hden : (0 : ℝ) < 8 * (K : ℝ) ^ 5 := by positivity
  have : (0 : ℝ) < (3 * (K : ℝ) ^ 2 + 2 * (K : ℝ) - 1) / (8 * (K : ℝ) ^ 5) :=
    div_pos hnum hden
  linarith

/-- Numerical core, for a general exponent `K + 1 ≥ 4`.

If `R, r > 0` satisfy `R^(K+1) ≥ 3/8`, `R^(K+1) + r^(K+1) ≥ 3/2` and `|R^K - r^K| ≤ 1/2`,
then `(1 + r (K+1)/K) R² / (R^(K+1) (R+r)) ≤ 2`. -/
private lemma second_deriv_A_aux (K : ℕ) (hK : 3 ≤ K) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (K + 1))
    (hm : |R ^ (K + 1) + r ^ (K + 1) - 2| ≤ 1 / 2)
    (hv : |R ^ K - r ^ K| ≤ 1 / 2) :
    (1 + r * (((K + 1 : ℕ) : ℝ)) / (((K : ℕ) : ℝ))) * R ^ 2
      / (R ^ (K + 1) * (R + r)) ≤ 2 := by
  have hK1le : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show (0 : ℕ) < K by omega)
  have hq : (((K + 1 : ℕ) : ℝ)) / (((K : ℕ) : ℝ)) = ((K : ℝ) + 1) / (K : ℝ) := by
    push_cast; ring
  have hsum : 3 / 2 ≤ R ^ (K + 1) + r ^ (K + 1) := by
    have h := (abs_le.mp hm).1
    linarith
  have hrub : r ^ K ≤ R ^ K + (1 : ℝ) / 2 := by
    have h := (abs_le.mp hv).1
    linarith
  have hRs : R ^ (K + 1) = R ^ K * R := pow_succ R K
  have hrs : r ^ (K + 1) = r ^ K * r := pow_succ r K
  -- (∗) : `R^K (R + r) ≥ (3 - r)/2`
  have hstar : (3 - r) / 2 ≤ R ^ K * (R + r) := by
    have h1 : r ^ (K + 1) ≤ r * (R ^ K + 1 / 2) := by
      rw [hrs]; nlinarith [hrub, hr]
    rw [hRs] at hsum
    nlinarith [hsum, h1, hr]
  -- `E ≥ (3 - F)/R`
  have hEF : (3 - (R + r + R * r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ)))) / R
      ≤ 2 * R ^ (K - 1) * (R + r) - 1 - r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ)) := by
    rw [div_le_iff₀ hR]
    have hs : R ^ (K - 1) * R = R ^ K := by rw [← pow_succ]; congr 1; omega
    have hthis : (2 * R ^ (K - 1) * (R + r) - 1
          - r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ))) * R
        = 2 * R ^ K * (R + r) - R - R * r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ)) := by
      rw [← hs]; ring
    rw [hthis]
    nlinarith [hstar]
  -- the goal follows from `E ≥ 0`
  have hgoal : (0 : ℝ) ≤ 2 * R ^ (K - 1) * (R + r) - 1
        - r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ)) →
      (1 + r * (((K + 1 : ℕ) : ℝ)) / (((K : ℕ) : ℝ))) * R ^ 2
        / (R ^ (K + 1) * (R + r)) ≤ 2 := by
    intro hE
    have hp : R ^ (K + 1) = R ^ (K - 1) * R ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [div_le_iff₀ (by positivity), hp]
    have h2 : (0 : ℝ) < R ^ 2 := by positivity
    have h3 : 0 ≤ (2 * R ^ (K - 1) * (R + r) - 1
        - r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ))) * R ^ 2 := mul_nonneg hE h2.le
    linear_combination h3
  by_cases hcase : (((K + 1 : ℕ) : ℝ)) / (((K : ℕ) : ℝ)) ≤ 2 * R ^ (K - 1)
  · -- CASE I : the coefficient of `r` in `E` is nonnegative
    have hc1 : ((K : ℝ) + 1) / (2 * (K : ℝ)) ≤ R ^ (K - 1) := by
      rw [hq] at hcase
      rw [div_le_iff₀ (by positivity)] at hcase ⊢
      linarith
    have hRb : (K : ℝ) / ((K : ℝ) + 1) ≤ R := by
      have hbnd : ((K : ℝ) / ((K : ℝ) + 1)) ^ (K + 1) ≤ 3 / 8 := by
        have h1 : (K : ℝ) / ((K : ℝ) + 1) = 1 - 1 / ((K + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        rw [h1]
        exact le_trans (Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast (show 1 ≤ K + 1 by omega)))
          exp_neg_one_lt_three_eighths.le
      exact (pow_le_pow_iff_left₀ (by positivity) hR.le (by omega)).mp (le_trans hbnd ha1)
    have hRK : (1 : ℝ) / 2 ≤ R ^ K := by
      have hs : R ^ K = R ^ (K - 1) * R := by rw [← pow_succ]; congr 1; omega
      rw [hs]
      have h2 : (1 : ℝ) / 2
          = ((K : ℝ) + 1) / (2 * (K : ℝ)) * ((K : ℝ) / ((K : ℝ) + 1)) := by
        field_simp
      rw [h2]
      exact mul_le_mul hc1 hRb (by positivity) (by positivity)
    have hEq : 2 * R ^ (K - 1) * (R + r) - 1 - r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ))
        = 2 * R ^ K - 1 + r * (2 * R ^ (K - 1) - (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ))) := by
      have hs : R ^ (K - 1) * R = R ^ K := by rw [← pow_succ]; congr 1; omega
      rw [← hs]; ring
    refine hgoal ?_
    rw [hEq]
    nlinarith [hRK, hcase, hr]
  · -- CASE II : the coefficient of `r` in `E` is negative
    simp only [not_le] at hcase
    have hRc : R ^ (K - 1) < ((K : ℝ) + 1) / (2 * (K : ℝ)) := by
      rw [hq] at hcase
      rw [lt_div_iff₀ hKpos] at hcase
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (K : ℝ))]
      linarith
    set U : ℝ := 1 - 1 / (2 * (K : ℝ)) with hU
    have hUval : U = 1 + -(1 / (2 * (K : ℝ))) := by rw [hU]; ring
    have hUpos : 0 < U := by
      rw [hU, sub_pos, div_lt_one (by positivity)]
      linarith [show (1 : ℝ) ≤ (K : ℝ) by exact_mod_cast hK1le]
    have hUbern : ((K : ℝ) + 1) / (2 * (K : ℝ)) ≤ U ^ (K - 1) := by
      have := bern_U K hK1le
      rwa [hUval]
    have hRU : R < U :=
      (pow_lt_pow_iff_left₀ hR.le hUpos.le (by omega)).mp (lt_of_lt_of_le hRc hUbern)
    -- `r ≤ 1 + (R^K - 1/2)/K`
    set rt : ℝ := 1 + (R ^ K - 1 / 2) / (K : ℝ) with hrt
    have hrle : r ≤ rt := by
      rw [hrt]
      exact rt_bound K hK1le hR hr hrub
    -- expand `F`
    have hcoef : (0 : ℝ) ≤ 1 + R * (((K : ℝ) + 1) / (K : ℝ)) := by positivity
    have hF1 : R + r + R * r * (((K : ℝ) + 1) / (K : ℝ))
        ≤ R + rt * (1 + R * (((K : ℝ) + 1) / (K : ℝ))) := by
      have he : R + r + R * r * (((K : ℝ) + 1) / (K : ℝ))
          = R + r * (1 + R * (((K : ℝ) + 1) / (K : ℝ))) := by ring
      rw [he]
      linarith [mul_le_mul_of_nonneg_right hrle hcoef]
    have hF2 : R + rt * (1 + R * (((K : ℝ) + 1) / (K : ℝ)))
        = (1 - 1 / (2 * (K : ℝ)))
          + (1 + ((K : ℝ) + 1) / (K : ℝ) - ((K : ℝ) + 1) / (2 * (K : ℝ) ^ 2)) * R
          + (1 / (K : ℝ)) * R ^ K + (((K : ℝ) + 1) / (K : ℝ) ^ 2) * R ^ (K + 1) := by
      rw [hrt]
      exact expand_F K hK1le R
    have hRKlt : R ^ K < ((K : ℝ) + 1) / (2 * (K : ℝ)) * R := by
      have hs : R ^ K = R ^ (K - 1) * R := by rw [← pow_succ]; congr 1; omega
      rw [hs]; exact mul_lt_mul_of_pos_right hRc hR
    have hRK1lt : R ^ (K + 1) < ((K : ℝ) + 1) / (2 * (K : ℝ)) * R ^ 2 := by
      have hs : R ^ (K + 1) = R ^ K * R := pow_succ R K
      rw [hs]
      calc R ^ K * R < (((K : ℝ) + 1) / (2 * (K : ℝ)) * R) * R := mul_lt_mul_of_pos_right hRKlt hR
        _ = ((K : ℝ) + 1) / (2 * (K : ℝ)) * R ^ 2 := by ring
    have hF3 : (1 - 1 / (2 * (K : ℝ)))
          + (1 + ((K : ℝ) + 1) / (K : ℝ) - ((K : ℝ) + 1) / (2 * (K : ℝ) ^ 2)) * R
          + (1 / (K : ℝ)) * R ^ K + (((K : ℝ) + 1) / (K : ℝ) ^ 2) * R ^ (K + 1)
        ≤ (1 - 1 / (2 * (K : ℝ))) + (1 + ((K : ℝ) + 1) / (K : ℝ)) * R
          + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * R ^ 2 := by
      have h1 : (1 / (K : ℝ)) * R ^ K ≤ (1 / (K : ℝ)) * (((K : ℝ) + 1) / (2 * (K : ℝ)) * R) :=
        mul_le_mul_of_nonneg_left hRKlt.le (by positivity)
      have h2 : (((K : ℝ) + 1) / (K : ℝ) ^ 2) * R ^ (K + 1)
          ≤ (((K : ℝ) + 1) / (K : ℝ) ^ 2) * (((K : ℝ) + 1) / (2 * (K : ℝ)) * R ^ 2) :=
        mul_le_mul_of_nonneg_left hRK1lt.le (by positivity)
      rw [← combine_F K hK1le R]
      linarith [h1, h2]
    have hRleU : R ≤ U := hRU.le
    have hF4 : (1 - 1 / (2 * (K : ℝ))) + (1 + ((K : ℝ) + 1) / (K : ℝ)) * R
          + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * R ^ 2
        ≤ (1 - 1 / (2 * (K : ℝ))) + (1 + ((K : ℝ) + 1) / (K : ℝ)) * U
          + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * U ^ 2 := by
      have h1 : (1 + ((K : ℝ) + 1) / (K : ℝ)) * R ≤ (1 + ((K : ℝ) + 1) / (K : ℝ)) * U :=
        mul_le_mul_of_nonneg_left hRleU (by positivity)
      have h2 : R ^ 2 ≤ U ^ 2 := by nlinarith [hRleU, hR.le, hUpos.le]
      have h3 : (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * R ^ 2
          ≤ (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * U ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith [h1, h3]
    have hF5 : (1 - 1 / (2 * (K : ℝ))) + (1 + ((K : ℝ) + 1) / (K : ℝ)) * U
          + (((K : ℝ) + 1) ^ 2 / (2 * (K : ℝ) ^ 3)) * U ^ 2 ≤ 3 := by
      rw [hUval]
      exact final_bound K hK1le
    have hFbound : R + r + R * r * (((K : ℝ) + 1) / (K : ℝ)) ≤ 3 :=
      le_trans hF1 (le_trans (le_of_eq hF2) (le_trans hF3 (le_trans hF4 hF5)))
    refine hgoal ?_
    have h3F : 0 ≤ 3 - (R + r + R * r * (((K : ℝ) + 1) / (K : ℝ))) := by linarith
    have hdiv : 0 ≤ (3 - (R + r + R * r * (((K + 1 : ℕ) : ℝ) / ((K : ℕ) : ℝ)))) / R := by
      rw [hq]
      exact div_nonneg h3F hR.le
    linarith [hEF, hdiv]

theorem second_deriv_A_le_two (n : ℕ) (hn : 1 ≤ n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (2 * n + 2)) (ha2 : R ^ (2 * n + 2) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r ^ (2 * n + 2)) (hb2 : r ^ (2 * n + 2) ≤ 15 / 8)
    (hm : |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ 1 / 2)
    (hv : |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ 1 / 2) :
    (1 + r * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R ^ 2
        / (R ^ (2 * n + 2) * (R + r)) ≤ 2 := by
  have h2n : (2 * n + 1) + 1 = 2 * n + 2 := by omega
  have hcast : (2 : ℝ) * n + 1 + 1 = 2 * n + 2 := by ring
  have h := second_deriv_A_aux (2 * n + 1) (by omega) hR hr
    (by simpa [h2n] using ha1) (by simpa [h2n] using hm) (by simpa using hv)
  have h' : (1 + r * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R ^ 2
      / (R ^ (2 * n + 2) * (R + r)) ≤ 2 := by simpa [hcast, h2n] using h
  convert h' using 1

end Work.OddCurve.LowSlope
