import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.logP_bounds
import Submission.Work.C17.logP_local_defs
import Submission.Work.C17.beukersD_two_sided
import Submission.Work.C17.beukersUR_two_sided

/-!
# `Work.C17.Pfun_hasSum` — convergence of the unlikely series `P` on `‖z‖ < x_s`

`Pfun a b ra rb rab r0 z` is the sum of the power series `Σ cₙ zⁿ`, `cₙ` the coefficients of
the unlikely `G`-function `Submission.CDT.logP a b ra rb rab r0` (paper eq. (defP)).  Here we
show that, whenever the coefficients are rational — i.e. under the assumed `ℤ`-linear relation
`r_a·η_a + r_b·η_b + r_ab·η_aη_b = r₀` (paper eq. (rabc)) — this series converges on the disc
`‖z‖ < xs a b`, the Taylor radius `x_s = (a+√(a²−1))·(b−√(b²−1))` of `P` (so that `Pfun` is
indeed the sum of its Taylor series there; this is the `hconv` hypothesis consumed by
`Work.C17.logP_local_structure`, `Work.C17f.Pfun_solves_M`, …).

The proof is the coefficient splitting `cₙ = κ·F n + K n` with

`κ = r_a + r_ab·η_b`, `F n = dₙ(a)·uₙ(b)`, `K n = (r_b + r_ab·η_a)·uₙ(a)·dₙ(b) + r_ab·dₙ(a)·dₙ(b)`

(`Work.C17.logPCoeffQ_eq_kap_Ffun_add_Kfun`), together with the two-sided sharp bounds

* `|dₙ(a)| ≤ C (n+1)²·α_a^{−n}` (`Work.C17.beukersD_two_sided`), `uₙ(b) ≤ α_bⁿ`
  (`Work.C17.beukersUR_two_sided`), giving `|F n| ≤ C₁ (n+1)³·x_s^{−n}`;
* the same bounds swapped, giving `|K n| ≤ C₂ (n+1)⁴·x_sⁿ` (`Work.C17.Kfun_bound`),

packaged by `Work.C17.logP_bounds`.  For `‖z‖ < x_s` the two majorants
`(n+1)³·(‖z‖/x_s)ⁿ` and `(n+1)⁴·(x_s‖z‖)ⁿ` are both geometrically summable (ratio `< 1`), so
`Σ cₙ zⁿ` is absolutely convergent, and the sum is `Pfun` by definition of `tsum`.
-/

namespace Work.C17

open scoped BigOperators

/-- `(n+1)^k·rⁿ` is summable for `‖r‖ < 1` (polynomial growth against a geometric series). -/
private lemma summable_succ_pow_mul_geometric (k : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have h : Summable (fun n : ℕ => ∑ j ∈ Finset.range (k + 1),
      ((k.choose j : ℝ) * (n : ℝ) ^ j) * r ^ n) := by
    refine summable_sum fun j hj => ?_
    exact ((summable_pow_mul_geometric_of_norm_lt_one j hr).mul_left (k.choose j : ℝ)).congr
      fun n => by ring
  refine h.congr fun n => ?_
  rw [add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [one_pow, mul_one]
  ring

theorem Pfun_hasSum (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (ra rb rab r0 : ℤ)
    (hrel : (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ) + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
      + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ)) = (r0 : ℝ)) :
    ∀ z : ℂ, ‖z‖ < xs a b →
      HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n)
        (Pfun a b ra rb rab r0 z) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  obtain ⟨hxspos, hxssq⟩ := xs_pos_and_sq_lt_one a b ha hb hab
  obtain ⟨cA, CA, hcA, hDA⟩ := beukersD_two_sided (a : ℝ) haR
  obtain ⟨cB, CB, hcB, hDB⟩ := beukersD_two_sided (b : ℝ) hbR
  have hApos : 0 < (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) := by
    have h := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1)
    have h2 : (0:ℝ) < (a:ℝ) := by linarith
    linarith
  have hBpos : 0 < (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) := by
    have h := Real.sqrt_nonneg ((b : ℝ) ^ 2 - 1)
    have h2 : (0:ℝ) < (b:ℝ) := by linarith
    linarith
  have hdalo : ∀ n : ℕ, min cA cB / (((n : ℝ) + 1) ^ 4 * ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n)
      ≤ |Submission.CDT.beukersD (a : ℝ) n| := by
    intro n
    refine le_trans (div_le_div_of_nonneg_right (min_le_left cA cB) ?_) (hDA n).2.1
    exact mul_nonneg (pow_nonneg (by positivity) 4) (pow_nonneg (le_of_lt hApos) n)
  have hdahi : ∀ n : ℕ, |Submission.CDT.beukersD (a : ℝ) n|
      ≤ max CA CB * ((n : ℝ) + 1) ^ 2 / ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n := by
    intro n
    refine le_trans (hDA n).2.2 ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left CA CB) (by positivity))
      (pow_nonneg (le_of_lt hApos) n)
  have hdbhi : ∀ n : ℕ, |Submission.CDT.beukersD (b : ℝ) n|
      ≤ max CA CB * ((n : ℝ) + 1) ^ 2 / ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n := by
    intro n
    refine le_trans (hDB n).2.2 ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right CA CB) (by positivity))
      (pow_nonneg (le_of_lt hBpos) n)
  have huahi : ∀ n : ℕ, Submission.CDT.beukersUR (a : ℝ) n
      ≤ ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ n :=
    fun n => (beukersUR_two_sided (a : ℝ) haR n).2
  have hublo : ∀ n : ℕ, ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n / ((n : ℝ) + 1)
      ≤ Submission.CDT.beukersUR (b : ℝ) n :=
    fun n => (beukersUR_two_sided (b : ℝ) hbR n).1
  have hubhi : ∀ n : ℕ, Submission.CDT.beukersUR (b : ℝ) n
      ≤ ((b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ n :=
    fun n => (beukersUR_two_sided (b : ℝ) hbR n).2
  obtain ⟨-, -, ⟨C1, hC1, hFub⟩, -, ⟨C2, hC2, hKub⟩⟩ :=
    logP_bounds a b ha hb hab ra rb rab (min cA cB) (max CA CB) (lt_min hcA hcB)
      hdalo hdahi hdbhi huahi hublo hubhi
  intro z hz
  have hsub : ∀ n : ℕ, ‖((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n‖
      ≤ |kap a b ra rab| * (C1 * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n) * ‖z‖ ^ n
        + C2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n * ‖z‖ ^ n := by
    intro n
    have hcoeff : ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℝ)
        = kap a b ra rab * Ffun a b n + Kfun a b ra rb rab n := by
      rw [← Submission.CDT.logPCoeff_logP a b ra rb rab r0 hrel n,
        Submission.CDT.logPCoeff_eq_rat a b ra rb rab r0 hrel n,
        logPCoeffQ_eq_kap_Ffun_add_Kfun a b ra rb rab r0 hrel n]
    have hnorm : ‖(((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ)) * z ^ n‖
        = |((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℝ)| * ‖z‖ ^ n := by
      rw [norm_mul, norm_pow, Complex.norm_ratCast]
    calc ‖((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n‖
        = |((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℝ)| * ‖z‖ ^ n := hnorm
      _ = |kap a b ra rab * Ffun a b n + Kfun a b ra rb rab n| * ‖z‖ ^ n := by
            rw [hcoeff]
      _ ≤ (|kap a b ra rab| * (C1 * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n)
            + C2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n) * ‖z‖ ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) n)
          calc |kap a b ra rab * Ffun a b n + Kfun a b ra rb rab n|
              ≤ |kap a b ra rab * Ffun a b n| + |Kfun a b ra rb rab n| :=
                abs_add_le _ _
            _ = |kap a b ra rab| * |Ffun a b n| + |Kfun a b ra rb rab n| := by
                rw [abs_mul]
            _ ≤ |kap a b ra rab| * (C1 * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n)
                  + C2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n :=
                add_le_add (mul_le_mul_of_nonneg_left (hFub n) (abs_nonneg _)) (hKub n)
      _ = |kap a b ra rab| * (C1 * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n) * ‖z‖ ^ n
            + C2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n * ‖z‖ ^ n := by ring
  have hr1 : ‖‖z‖ / xs a b‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (le_of_lt hxspos))]
    rw [div_lt_one hxspos]
    exact hz
  have hr2 : ‖xs a b * ‖z‖‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hxspos) (norm_nonneg _))]
    have hlt : xs a b * ‖z‖ < xs a b * xs a b := mul_lt_mul_of_pos_left hz hxspos
    linarith
  have hsum1 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 3 * (‖z‖ / xs a b) ^ n) :=
    summable_succ_pow_mul_geometric 3 hr1
  have hsum2 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * (xs a b * ‖z‖) ^ n) :=
    summable_succ_pow_mul_geometric 4 hr2
  have hmaj : Summable (fun n : ℕ =>
      |kap a b ra rab| * (C1 * ((n : ℝ) + 1) ^ 3 / (xs a b) ^ n) * ‖z‖ ^ n
        + C2 * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n * ‖z‖ ^ n) := by
    refine ((hsum1.mul_left (|kap a b ra rab| * C1)).add
      (hsum2.mul_left C2)).congr fun n => ?_
    simp only [div_pow, mul_pow]
    ring
  have hsumC : Summable (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hsub hmaj)
  simpa only [Pfun] using hsumC.hasSum

end Work.C17
