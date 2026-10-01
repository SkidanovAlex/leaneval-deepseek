/-
# Elementary auxiliary estimates for the BGTZ detector

* `rpow_mul_one_sub_le` — the weighted-AM-GM bound `u^δ(1-u) ≤ δ^δ/(1+δ)^{1+δ}` on `[0,1]`;
* `aCoeff_nonneg` — `a(n) = Σ_{d|n}χ₁(d) ≥ 0` for a real character (`Work.Sieve.aFun_basics`);
* `pointwise_le`, `smoothed_le_sum` — the pointwise/summed comparisons
  `a(n)n^{-β₁}(1-n/R) ≤ (a(n)/n)·(1-β₁)^{1-β₁}R^{1-β₁}/(2-β₁)^{2-β₁}` (the "bracket" that converts
  the smoothed lower bound into a lower bound for `Σ_{n ≤ R}a(n)/n` keeping the factor `R^{1-β₁}`);
* `aCoeff_one`, `totient_ratio`, `denom_bound` — bookkeeping (`a(1) = 1`, `(φ(q)/q)(q/φ(q)) = 1`,
  `|(1-ρ)(2-ρ)| ≥ (1-Re ρ)(2-Re ρ)`).
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.Sieve.aFun_basics

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

lemma rpow_mul_one_sub_le {δ u : ℝ} (hδ : 0 < δ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u ^ δ * (1 - u) ≤ δ ^ δ / (1 + δ) ^ (1 + δ) := by
  have h1δ : 0 < 1 + δ := by linarith
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · rw [← h0, Real.zero_rpow hδ.ne', zero_mul]
    positivity
  · have hA0 : 0 ≤ u * (1 + δ) / δ := by positivity
    have hB0 : 0 ≤ (1 + δ) * (1 - u) := by nlinarith
    have hsum : δ * (u * (1 + δ) / δ) + (1 + δ) * (1 - u) = 1 + δ := by
      rw [mul_div_cancel₀ _ hδ.ne']
      ring
    have hw1 : 0 ≤ δ / (1 + δ) := by positivity
    have hw2 : 0 ≤ 1 / (1 + δ) := by positivity
    have hw : δ / (1 + δ) + 1 / (1 + δ) = 1 := by
      rw [← add_div, show δ + 1 = 1 + δ by ring, div_self h1δ.ne']
    have hamgm : (u * (1 + δ) / δ) ^ (δ / (1 + δ)) * ((1 + δ) * (1 - u)) ^ (1 / (1 + δ))
        ≤ (δ / (1 + δ)) * (u * (1 + δ) / δ) + (1 / (1 + δ)) * ((1 + δ) * (1 - u)) :=
      Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hA0 hB0 hw
    have hrhs : (δ / (1 + δ)) * (u * (1 + δ) / δ) + (1 / (1 + δ)) * ((1 + δ) * (1 - u)) = 1 := by
      have h1 : (δ / (1 + δ)) * (u * (1 + δ) / δ) + (1 / (1 + δ)) * ((1 + δ) * (1 - u))
          = (δ * (u * (1 + δ) / δ) + (1 + δ) * (1 - u)) / (1 + δ) := by
        field_simp
      rw [h1, hsum, div_self h1δ.ne']
    have hle1 : (u * (1 + δ) / δ) ^ (δ / (1 + δ)) * ((1 + δ) * (1 - u)) ^ (1 / (1 + δ)) ≤ 1 :=
      hamgm.trans (le_of_eq hrhs)
    have h2 : (u * (1 + δ) / δ) ^ δ * ((1 + δ) * (1 - u))
        = ((u * (1 + δ) / δ) ^ (δ / (1 + δ)) * ((1 + δ) * (1 - u)) ^ (1 / (1 + δ))) ^ (1 + δ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)]
      rw [← Real.rpow_mul hA0, ← Real.rpow_mul hB0]
      have e1 : δ / (1 + δ) * (1 + δ) = δ := by field_simp
      have e2 : 1 / (1 + δ) * (1 + δ) = 1 := by field_simp
      rw [e1, e2, Real.rpow_one]
    have h3 : (u * (1 + δ) / δ) ^ δ * ((1 + δ) * (1 - u)) ≤ 1 := by
      rw [h2]
      calc (((u * (1 + δ) / δ) ^ (δ / (1 + δ)) * ((1 + δ) * (1 - u)) ^ (1 / (1 + δ))) ^ (1 + δ))
          ≤ (1 : ℝ) ^ (1 + δ) := Real.rpow_le_rpow (by positivity) hle1 (by linarith)
        _ = 1 := Real.one_rpow _
    have hp : (1 + δ) ^ (1 + δ) = (1 + δ) ^ (1:ℝ) * (1 + δ) ^ δ := by
      rw [← Real.rpow_add h1δ]
    have hAδ : (u * (1 + δ) / δ) ^ δ * ((1 + δ) * (1 - u))
        = u ^ δ * (1 - u) * ((1 + δ) ^ (1 + δ) / δ ^ δ) := by
      rw [Real.div_rpow (by positivity) hδ.le, Real.mul_rpow hu0 h1δ.le, hp, Real.rpow_one]
      field_simp
    have h4 : u ^ δ * (1 - u) * ((1 + δ) ^ (1 + δ) / δ ^ δ) ≤ 1 := hAδ ▸ h3
    have hK : 0 < (1 + δ) ^ (1 + δ) := by positivity
    have h5 : u ^ δ * (1 - u) * (1 + δ) ^ (1 + δ) ≤ δ ^ δ := by
      have hm := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ δ ^ δ)
      rw [one_mul] at hm
      calc u ^ δ * (1 - u) * (1 + δ) ^ (1 + δ)
          = u ^ δ * (1 - u) * ((1 + δ) ^ (1 + δ) / δ ^ δ) * δ ^ δ := by
            field_simp
        _ ≤ δ ^ δ := hm
    rw [le_div_iff₀ hK]
    exact h5


lemma aCoeff_nonneg (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (n : ℕ) :
    0 ≤ aCoeff χ₁ n := by
  have h := (Work.Sieve.aFun_basics χ₁ hχ₁).2.1 n
  simpa [aCoeff, Work.LinnikAreas.Sieve.aFun] using h

-- the pointwise bound
lemma pointwise_le (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {β₁ : ℝ} (hβ₁ : β₁ < 1) {R n : ℕ} (hn1 : 1 ≤ n) (hnR : n ≤ R) :
    aCoeff χ₁ n * (n : ℝ) ^ (-β₁) * (1 - (n : ℝ) / (R : ℝ))
      ≤ (aCoeff χ₁ n / (n : ℝ))
          * ((1 - β₁) ^ (1 - β₁) * (R : ℝ) ^ (1 - β₁) / (2 - β₁) ^ (2 - β₁)) := by
  have hδ : 0 < 1 - β₁ := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hR0 : 0 < (R : ℝ) := by exact_mod_cast (le_trans hn1 hnR)
  have ha : 0 ≤ aCoeff χ₁ n := aCoeff_nonneg χ₁ hχ₁ n
  have hu0 : 0 ≤ (n : ℝ) / (R : ℝ) := by positivity
  have hu1 : (n : ℝ) / (R : ℝ) ≤ 1 := by
    rw [div_le_one hR0]; exact_mod_cast hnR
  have ham := rpow_mul_one_sub_le hδ hu0 hu1
  have h1p : (1 : ℝ) + (1 - β₁) = 2 - β₁ := by ring
  rw [h1p] at ham
  have hRδ : 0 < (R : ℝ) ^ (1 - β₁) := Real.rpow_pos_of_pos hR0 _
  have hkey : (n : ℝ) ^ (1 - β₁) * (1 - (n : ℝ) / (R : ℝ))
      ≤ (1 - β₁) ^ (1 - β₁) * (R : ℝ) ^ (1 - β₁) / (2 - β₁) ^ (2 - β₁) := by
    have hnRδ : (n : ℝ) ^ (1 - β₁)
        = (R : ℝ) ^ (1 - β₁) * ((n : ℝ) / (R : ℝ)) ^ (1 - β₁) := by
      rw [Real.div_rpow (le_of_lt hn0) (le_of_lt hR0)]
      field_simp
    rw [hnRδ]
    calc (R : ℝ) ^ (1 - β₁) * ((n : ℝ) / (R : ℝ)) ^ (1 - β₁) * (1 - (n : ℝ) / (R : ℝ))
        = (R : ℝ) ^ (1 - β₁)
            * (((n : ℝ) / (R : ℝ)) ^ (1 - β₁) * (1 - (n : ℝ) / (R : ℝ))) := by ring
      _ ≤ (R : ℝ) ^ (1 - β₁) * ((1 - β₁) ^ (1 - β₁) / (2 - β₁) ^ (2 - β₁)) :=
          mul_le_mul_of_nonneg_left ham hRδ.le
      _ = (1 - β₁) ^ (1 - β₁) * (R : ℝ) ^ (1 - β₁) / (2 - β₁) ^ (2 - β₁) := by ring
  have hfac : aCoeff χ₁ n * (n : ℝ) ^ (-β₁) * (1 - (n : ℝ) / (R : ℝ))
      = (aCoeff χ₁ n / (n : ℝ))
          * ((n : ℝ) ^ (1 - β₁) * (1 - (n : ℝ) / (R : ℝ))) := by
    have hexp : (n : ℝ) ^ (-β₁) = (n : ℝ) ^ (-1:ℝ) * (n : ℝ) ^ (1 - β₁) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [hexp, Real.rpow_neg_one]
    field_simp
  rw [hfac]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

-- the summed version (the "bracket" estimate)
lemma smoothed_le_sum (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {β₁ : ℝ} (hβ₁ : β₁ < 1) {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n * (n : ℝ) ^ (-β₁) * (1 - (n : ℝ) / (R : ℝ)))
      ≤ (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))
          * ((1 - β₁) ^ (1 - β₁) * (R : ℝ) ^ (1 - β₁) / (2 - β₁) ^ (2 - β₁)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  exact pointwise_le χ₁ hχ₁ hβ₁ hn.1 hn.2



/-- The modulus of `(1-ρ)(2-ρ)` is at least `(1-Re ρ)(2-Re ρ)`. -/
lemma denom_bound {ρ : ℂ} (hre : 1 / 2 < ρ.re) (hre1 : ρ.re < 1) :
    (1 - ρ.re) * (2 - ρ.re) ≤ ‖(1 - ρ) * (2 - ρ)‖ := by
  have h1 : 1 - ρ.re ≤ ‖(1 : ℂ) - ρ‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) - ρ)
    rw [Complex.sub_re, Complex.one_re] at h
    linarith [le_abs_self (1 - ρ.re)]
  have h2 : 2 - ρ.re ≤ ‖(2 : ℂ) - ρ‖ := by
    have h := Complex.abs_re_le_norm ((2 : ℂ) - ρ)
    have h2' : ((2 : ℂ) - ρ).re = 2 - ρ.re := by simp [Complex.sub_re]
    rw [h2'] at h
    linarith [le_abs_self (2 - ρ.re)]
  rw [norm_mul]
  exact mul_le_mul h1 h2 (by linarith) (norm_nonneg _)

lemma totient_ratio {q : ℕ} [NeZero q] :
    ((q.totient : ℝ) / (q : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) = 1 := by
  have h1 : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have h2 : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  field_simp

lemma aCoeff_one (χ₁ : DirichletCharacter ℂ q) : aCoeff χ₁ 1 = 1 := by
  rw [aCoeff, Nat.divisors_one, Finset.sum_singleton]
  simp

end Work.LinnikAreas.BGTZ
