import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.RegionIII.caRegionIIIDefs

/-!
# Region III: the two numeric bounds of the `caC1` assembly

* `main_term_aux`: the main (Abel) term of `sum_prime_inv_sq_lower_A2`,
  `(1/(n log n))·(1 − n/ξ − 1/log n)`, is at least `1.075/(√ξ log ξ)`.
* `third_term_aux`: the subtracted `(1/3)/n²` term is at most `0.0011/(√ξ log ξ)`.

Combined with the correction bound `≤ 0.181/(√ξ log ξ)` (delegated) and
`S2 ≥ main − corr`, this yields `(1/2)·S2 − (1/3)/n² ≥ 0.44/(√ξ log ξ)`.
-/

namespace Work.RHContract.A.RegionIII

noncomputable section

/-- The main Abel term dominates `1.075/(√ξ·log ξ)`. -/
theorem main_term_aux {ξ L : ℝ} {n : ℕ}
    (hξ : (10 : ℝ) ^ 8 ≤ ξ) (hL18 : 18.2 ≤ L)
    (hlogn_lo : (L + 0.88) / 2 ≤ Real.log (n : ℝ))
    (hlogn_hi : Real.log (n : ℝ) ≤ (L + 0.95) / 2)
    (hn_hi : (n : ℝ) ≤ 1.58125 * Real.sqrt ξ) :
    (1.075 : ℝ) ≤ (1 / ((n : ℝ) * Real.log (n : ℝ)))
        * (1 - (n : ℝ) / ξ - 1 / Real.log (n : ℝ)) * (Real.sqrt ξ * L) := by
  have hξpos : 0 < ξ := by linarith
  have hspos : 0 < Real.sqrt ξ := Real.sqrt_pos_of_pos hξpos
  have hs2 : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt (le_of_lt hξpos)
  have hsge : (10 : ℝ) ^ 4 ≤ Real.sqrt ξ := by
    have h := Real.sqrt_le_sqrt hξ
    have h10 : Real.sqrt ((10 : ℝ) ^ 8) = (10 : ℝ) ^ 4 := by
      rw [show (10 : ℝ) ^ 8 = ((10 : ℝ) ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h10] at h
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hnpos : 0 < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at hlogn_pos
    · exact_mod_cast h
  have hnlogpos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hnpos hlogn_pos
  have hnumpos : 0 < 1.58125 * Real.sqrt ξ * (L + 0.95) :=
    mul_pos (mul_pos (by norm_num) hspos) (by linarith)
  have hkey1 : 2 / (1.58125 * Real.sqrt ξ * (L + 0.95)) ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
    rw [div_le_div_iff₀ hnumpos hnlogpos]
    have h1 : (n : ℝ) * Real.log (n : ℝ) ≤ 1.58125 * Real.sqrt ξ * ((L + 0.95) / 2) :=
      mul_le_mul hn_hi hlogn_hi (le_of_lt hlogn_pos) (by positivity)
    nlinarith [h1]
  have hterm : (0.895 : ℝ) ≤ 1 - (n : ℝ) / ξ - 1 / Real.log (n : ℝ) := by
    have h1 : (n : ℝ) / ξ ≤ 1.58125 / Real.sqrt ξ := by
      rw [div_le_div_iff₀ hξpos hspos]
      nlinarith [hn_hi, hs2, hspos]
    have h2 : 1 / Real.log (n : ℝ) ≤ 2 / (L + 0.88) := by
      rw [div_le_div_iff₀ hlogn_pos (by linarith : (0 : ℝ) < L + 0.88)]
      nlinarith [hlogn_lo]
    have h3 : 1.58125 / Real.sqrt ξ ≤ 1.58125 / 10000 := by
      rw [div_le_div_iff₀ hspos (by norm_num)]
      nlinarith [hsge]
    have h4 : 2 / (L + 0.88) ≤ 2 / 19.08 := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < L + 0.88) (by norm_num)]
      linarith
    have hnum : (1 : ℝ) - 1.58125 / 10000 - 2 / 19.08 ≥ 0.895 := by norm_num
    linarith
  have hkey3 : (1.075 : ℝ) ≤
      2 / (1.58125 * Real.sqrt ξ * (L + 0.95)) * 0.895 * (Real.sqrt ξ * L) := by
    have hden : (1.58125 * Real.sqrt ξ * (L + 0.95)) ≠ 0 :=
      ne_of_gt (mul_pos (mul_pos (by norm_num) hspos) (by linarith))
    have hden2 : (L + 0.95) ≠ 0 := by linarith
    have hEq : 2 / (1.58125 * Real.sqrt ξ * (L + 0.95)) * 0.895 * (Real.sqrt ξ * L)
        = (1.79 / 1.58125) * (L / (L + 0.95)) := by
      field_simp
      ring
    rw [hEq]
    have hfrac : (18.2 : ℝ) / 19.15 ≤ L / (L + 0.95) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have hstep : (1.79 / 1.58125) * ((18.2 : ℝ) / 19.15) ≤
        (1.79 / 1.58125) * (L / (L + 0.95)) :=
      mul_le_mul_of_nonneg_left hfrac (by norm_num)
    have hnum : (1.075 : ℝ) ≤ (1.79 / 1.58125) * ((18.2 : ℝ) / 19.15) := by norm_num
    linarith
  calc (1.075 : ℝ)
      ≤ 2 / (1.58125 * Real.sqrt ξ * (L + 0.95)) * 0.895 * (Real.sqrt ξ * L) := hkey3
    _ ≤ (1 / ((n : ℝ) * Real.log (n : ℝ))) * (1 - (n : ℝ) / ξ - 1 / Real.log (n : ℝ))
          * (Real.sqrt ξ * L) := by
        have hm : 2 / (1.58125 * Real.sqrt ξ * (L + 0.95)) * 0.895
            ≤ (1 / ((n : ℝ) * Real.log (n : ℝ))) * (1 - (n : ℝ) / ξ - 1 / Real.log (n : ℝ)) :=
          mul_le_mul hkey1 hterm (by norm_num) (le_of_lt (one_div_pos.mpr hnlogpos))
        have hsL : 0 ≤ Real.sqrt ξ * L := by positivity
        exact mul_le_mul_of_nonneg_right hm hsL

/-- The subtracted `(1/3)/n²` term, scaled by `√ξ·log ξ`, is at most `0.0011`. -/
theorem third_term_aux {ξ L : ℝ} {n : ℕ}
    (hξ : (10 : ℝ) ^ 8 ≤ ξ) (hLpos : 0 ≤ L) (hnpos : 0 < (n : ℝ))
    (hn2 : 2.5 * ξ ≤ (n : ℝ) ^ 2)
    (hL8 : L ≤ 8 * ξ ^ (1 / 8 : ℝ))
    (hxi38 : (1000 : ℝ) ≤ ξ ^ (3 / 8 : ℝ)) :
    (1 / 3) * (1 / ((n : ℝ) ^ 2)) * (Real.sqrt ξ * L) ≤ 0.0011 := by
  have hξpos : 0 < ξ := by linarith
  have hspos : 0 < Real.sqrt ξ := Real.sqrt_pos_of_pos hξpos
  have h1 : 1 / ((n : ℝ) ^ 2) ≤ 1 / (2.5 * ξ) :=
    one_div_le_one_div_of_le (by linarith) hn2
  have h2 : Real.sqrt ξ * L ≤ Real.sqrt ξ * (8 * ξ ^ (1 / 8 : ℝ)) :=
    mul_le_mul_of_nonneg_left hL8 (le_of_lt hspos)
  have hstep : (1 / 3) * (1 / ((n : ℝ) ^ 2)) * (Real.sqrt ξ * L)
      ≤ (1 / 3) * (1 / (2.5 * ξ)) * (Real.sqrt ξ * (8 * ξ ^ (1 / 8 : ℝ))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
      (by positivity) (by positivity)
  have halg : (1 / 3) * (1 / (2.5 * ξ)) * (Real.sqrt ξ * (8 * ξ ^ (1 / 8 : ℝ)))
      = (8 / 7.5) * ξ ^ (-(3 / 8) : ℝ) := by
    have h1' : Real.sqrt ξ * ξ ^ (1 / 8 : ℝ) = ξ ^ (5 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hξpos (1 / 2) (1 / 8)]
      norm_num
    have h3 : ξ ^ (5 / 8 : ℝ) / ξ = ξ ^ (-(3 / 8) : ℝ) := by
      have h := Real.rpow_sub hξpos (5 / 8 : ℝ) 1
      rw [Real.rpow_one] at h
      have hpow : (5 : ℝ) / 8 - 1 = -(3 / 8) := by norm_num
      rw [hpow] at h
      exact h.symm
    rw [show (1 / 3) * (1 / (2.5 * ξ)) * (Real.sqrt ξ * (8 * ξ ^ (1 / 8 : ℝ)))
        = (8 / 7.5) * ((Real.sqrt ξ * ξ ^ (1 / 8 : ℝ)) / ξ) by field_simp; ring]
    rw [h1', h3]
  have hrec : ξ ^ (-(3 / 8) : ℝ) ≤ 1 / 1000 := by
    rw [Real.rpow_neg (le_of_lt hξpos), one_div,
      inv_le_inv₀ (Real.rpow_pos_of_pos hξpos (3 / 8)) (by norm_num : (0 : ℝ) < 1000)]
    exact hxi38
  have hfinal : (8 / 7.5) * ξ ^ (-(3 / 8) : ℝ) ≤ 0.0011 := by
    have h := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 8 / 7.5)
    nlinarith [h]
  linarith [hstep, halg.le, halg.ge, hfinal]

end

end Work.RHContract.A.RegionIII
