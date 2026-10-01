import Mathlib
import Submission.Commons.NumberTheory.DirichletSeries.omega_euler_product
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

namespace Work.LinnikAreas.CorrAllR

/-- **Final arithmetic for the general-`r` cube-free moment bound.**

For `r ≥ 1` and `ε > 0` there is `C > 0` such that for all `q ≥ 1` and all `H`,
```
(2r)^(ω q) · √q · ((2r) · 2^(2r-1) · H^(2r) · d(q)^(2r-1))  +  q · ((2r)^(2r) · H^r)
        ≤  C · q^ε · (q H^r + H^(2r) √q).
```
(`ω q = q.primeFactors.card`, `d(q) = q.divisors.card`.)

Route: `q^ε ≥ 1` (as `q ≥ 1`) handles the second term with the constant `(2r)^(2r)`; for the first
term bound `(2r)^(ω q) ≤ C₁ q^(ε/2)` and `d(q)^(2r-1) ≤ C₂ q^(ε/2)` using
`Commons.NumberTheory.DirichletSeries.pow_card_primeFactors_le_const_mul_rpow` (base `2r`,
exponent `ε/2`) and `Commons.NumberTheory.DivisorBound.card_divisors_le_rpow` (exponent
`ε/(4(2r-1))`, legitimate since `2r-1 ≥ 1`), and combine.  `H = 0` and `H ≥ 1` should be split. -/
theorem final_arith (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q H : ℕ), 1 ≤ q →
      ((2 * r : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
          ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
            * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1))
        + (q : ℝ) * ((2 * r : ℝ) ^ (2 * r) * (H : ℝ) ^ r))
      ≤ C * (q : ℝ) ^ ε
          * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hε4r : (0 : ℝ) < ε / (4 * (r : ℝ)) := by positivity
  obtain ⟨Cω, hCωpos, hCωb⟩ :=
    Commons.NumberTheory.DirichletSeries.pow_card_primeFactors_le_const_mul_rpow
      (2 * (r : ℝ)) (ε / (4 * (r : ℝ))) (by positivity) hε4r
  obtain ⟨Cd, hCdpos, hCdb⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (ε / (4 * (r : ℝ))) hε4r
  refine ⟨Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * 2 ^ (2 * r - 1)) + (2 * r) ^ (2 * r) + 1,
    by positivity, ?_⟩
  intro q H hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqε0 : (0 : ℝ) ≤ (q : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hqε1 : (1 : ℝ) ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq1 hε.le
  have hHr0 : (0 : ℝ) ≤ (H : ℝ) ^ r := by positivity
  have hH2r0 : (0 : ℝ) ≤ (H : ℝ) ^ (2 * r) := by positivity
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hqH0 : (0 : ℝ) ≤ (q : ℝ) * (H : ℝ) ^ r := mul_nonneg (Nat.cast_nonneg q) hHr0
  have hsq : (0 : ℝ) ≤ (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ) := mul_nonneg hH2r0 hsq0
  -- `(2r)^(ω q) ≤ Cω q^(ε/2)`
  have hexp1 : ε / (4 * (r : ℝ)) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε.le, hr1]
  have hCg_abs : (2 * r : ℝ) ^ q.primeFactors.card ≤ Cω * (q : ℝ) ^ (ε / 2) :=
    (hCωb q hq).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hexp1)
        (le_of_lt hCωpos))
  -- `d(q)^(2r-1) ≤ Cd^(2r-1) q^(ε/2)`
  have hτ_abs : ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1)
      ≤ Cd ^ (2 * r - 1) * (q : ℝ) ^ (ε / 2) := by
    refine (pow_le_pow_left₀ (by positivity) (hCdb q) (2 * r - 1)).trans ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt hCdpos) _)
    have hb1 : (1 : ℝ) ≤ (q : ℝ) ^ (ε / (4 * (r : ℝ))) :=
      Real.one_le_rpow hq1 (by positivity)
    have h1 : ((q : ℝ) ^ (ε / (4 * (r : ℝ)))) ^ (2 * r - 1)
        ≤ ((q : ℝ) ^ (ε / (4 * (r : ℝ)))) ^ (2 * r) :=
      pow_le_pow_right₀ hb1 (by omega)
    have h2 : ((q : ℝ) ^ (ε / (4 * (r : ℝ)))) ^ (2 * r) = (q : ℝ) ^ (ε / 2) := by
      have h3 : ((q : ℝ) ^ (ε / (4 * (r : ℝ)))) ^ (2 * r)
          = (q : ℝ) ^ ((ε / (4 * (r : ℝ))) * ((2 * r : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast ((q : ℝ) ^ (ε / (4 * (r : ℝ)))) (2 * r)]
        exact (Real.rpow_mul (Nat.cast_nonneg q) (ε / (4 * (r : ℝ)))
          ((2 * r : ℕ) : ℝ)).symm
      have hexp : (ε / (4 * (r : ℝ))) * ((2 * r : ℕ) : ℝ) = ε / 2 := by
        push_cast
        field_simp
        ring
      rw [h3, hexp]
    exact h1.trans (le_of_eq h2)
  -- first summand
  have hA1 : (2 * r : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ)
        * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
            * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1))
      ≤ Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
          * ((q : ℝ) ^ ε * ((H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) := by
    have h2 := mul_le_mul_of_nonneg_right hCg_abs hsq0
    have h3 : (H : ℝ) ^ (2 * r) * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1)
        ≤ (H : ℝ) ^ (2 * r) * (Cd ^ (2 * r - 1) * (q : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hτ_abs hH2r0
    have h4 : (2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1)
          * ((H : ℝ) ^ (2 * r) * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1))
        ≤ (2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1)
          * ((H : ℝ) ^ (2 * r) * (Cd ^ (2 * r - 1) * (q : ℝ) ^ (ε / 2))) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have hpow : (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ ε := by
      rw [← Real.rpow_add hqpos]
      congr 1
      ring
    calc (2 * r : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ)
          * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
              * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1))
        = ((2 * r : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ))
          * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1)
              * ((H : ℝ) ^ (2 * r) * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1))) := by ring
      _ ≤ ((Cω * (q : ℝ) ^ (ε / 2)) * Real.sqrt (q : ℝ))
          * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1)
              * ((H : ℝ) ^ (2 * r) * (Cd ^ (2 * r - 1) * (q : ℝ) ^ (ε / 2)))) :=
          mul_le_mul h2 h4 (by positivity) (by positivity)
      _ = Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
          * (((q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2))
              * ((H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) := by ring
      _ = Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
          * ((q : ℝ) ^ ε * ((H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) := by rw [hpow]
  -- second summand
  have hA2 : (q : ℝ) * ((2 * r : ℝ) ^ (2 * r) * (H : ℝ) ^ r)
      ≤ (2 * r : ℝ) ^ (2 * r)
          * ((q : ℝ) ^ ε
              * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) := by
    have hkey : (H : ℝ) ^ r * (q : ℝ)
        ≤ (q : ℝ) ^ ε
            * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)) := by
      have h1 : (H : ℝ) ^ r * (q : ℝ) ≤ (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ r) := by
        have hqq : (q : ℝ) ≤ (q : ℝ) ^ ε * (q : ℝ) := by
          simpa using mul_le_mul_of_nonneg_right hqε1 (Nat.cast_nonneg q)
        calc (H : ℝ) ^ r * (q : ℝ) ≤ (H : ℝ) ^ r * ((q : ℝ) ^ ε * (q : ℝ)) :=
              mul_le_mul_of_nonneg_left hqq hHr0
          _ = (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ r) := by ring
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hqε0
      linarith [hqH0, hsq]
    calc (q : ℝ) * ((2 * r : ℝ) ^ (2 * r) * (H : ℝ) ^ r)
        = (2 * r : ℝ) ^ (2 * r) * ((H : ℝ) ^ r * (q : ℝ)) := by ring
      _ ≤ (2 * r : ℝ) ^ (2 * r)
          * ((q : ℝ) ^ ε
              * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
  -- combine
  have hX0 : (0 : ℝ) ≤ (q : ℝ) ^ ε
      * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)) :=
    mul_nonneg hqε0 (add_nonneg hqH0 hsq)
  have hA0 : (0 : ℝ) ≤ Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1)) := by
    positivity
  have hB0 : (0 : ℝ) ≤ (2 * r : ℝ) ^ (2 * r) := by positivity
  have hle : (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)
      ≤ (q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ) := by
    linarith [hqH0]
  have hfin : Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
        * ((q : ℝ) ^ ε * ((H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
      + (2 * r : ℝ) ^ (2 * r)
        * ((q : ℝ) ^ ε
            * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
      ≤ (Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * 2 ^ (2 * r - 1)) + (2 * r) ^ (2 * r) + 1)
        * (q : ℝ) ^ ε
        * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)) := by
    have hstep1 : Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
          * ((q : ℝ) ^ ε * ((H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
        ≤ Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
          * ((q : ℝ) ^ ε
              * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hqε0) hA0
    calc Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
          * ((q : ℝ) ^ ε * ((H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
        + (2 * r : ℝ) ^ (2 * r)
          * ((q : ℝ) ^ ε
              * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
        ≤ Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
            * ((q : ℝ) ^ ε
                * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
          + (2 * r : ℝ) ^ (2 * r)
            * ((q : ℝ) ^ ε
                * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) :=
          add_le_add hstep1 (le_refl _)
      _ = (Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
            + (2 * r : ℝ) ^ (2 * r))
          * ((q : ℝ) ^ ε
              * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) := by ring
      _ ≤ (Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * 2 ^ (2 * r - 1)) + (2 * r) ^ (2 * r) + 1)
          * ((q : ℝ) ^ ε
              * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ hX0
          have : Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1))
              + (2 * r : ℝ) ^ (2 * r)
              ≤ Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * 2 ^ (2 * r - 1))
                + (2 * r) ^ (2 * r) + 1 := by linarith
          exact this
      _ = (Cω * Cd ^ (2 * r - 1) * ((2 * r : ℝ) * 2 ^ (2 * r - 1)) + (2 * r) ^ (2 * r) + 1)
          * (q : ℝ) ^ ε
          * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)) := by ring
  exact (add_le_add hA1 hA2).trans hfin

end Work.LinnikAreas.CorrAllR
