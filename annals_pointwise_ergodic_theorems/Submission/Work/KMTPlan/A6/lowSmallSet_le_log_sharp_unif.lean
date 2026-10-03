import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log_sharp

namespace Work.KMTPlan.A6

open scoped NNReal

/-- **The sharp, uniform-in-`Λ` count of the small-scale index set.**

A scale `N = ⌊a n⌋` that is admissible (`inIndexSet`) and small
(`N ≤ splitCut ρ L`, `L = lcL l₁ l₂ k₁ k₂`, `u = uScale ρ L`) forces
`n + 1 ≤ (2 log 2 / log Λ + 3) · 2^u`, with a constant that depends only on `Λ` and is
uniform in `L`.

Unlike `lowSmallSet_le_log_sharp` this needs **no** lower threshold on `L`: for small `u`
(`2^u ≥ 1` is all that is used) the generous constant `2 log 2 / log Λ + 3` absorbs the
`+ 1` of `n + 1` directly, while for large `L` the lacunary growth
`Λ^n ≤ a n < 2^{2^u} + 1` gives `n < (2^u + 1) log 2 / log Λ`, and turning `1 ≤ 2^u` into
the two extra copies of `2^u` in the factor `2 c + 3` (`c = log 2 / log Λ`) closes the
estimate. -/
theorem lowSmallSet_le_log_sharp_unif (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) :
    ∀ (Λ : NNReal), 1 < Λ → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ (l₁ l₂ k₁ k₂ n : ℕ),
        Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
        (n : ℝ) + 1 ≤ (2 * Real.log 2 / Real.log (Λ : ℝ) + 3)
          * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) := by
  intro Λ hΛ a ha ha1 l₁ l₂ k₁ k₂ n hsm
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨-, hle⟩ := hsm
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hU
  set c : ℝ := Real.log 2 / Real.log (Λ : ℝ) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (le_of_lt hlog2) (le_of_lt hlogΛ)
  -- the small-scale threshold
  have hSle : Nat.floor (a n)
      ≤ Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := hle
  have hS1 : 1 ≤ Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := by
    rw [Work.KMTAreas.A7.splitCut]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hS1R : (1 : ℝ)
      ≤ (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) := by
    exact_mod_cast hS1
  have hSpos : (0 : ℝ)
      < (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS1)
  -- `a n < splitCut + 1`
  have han : (a n : ℝ)
      < (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) + 1 := by
    have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℝ≥0) : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (a n)
    have h2 : ((Nat.floor (a n) : ℝ≥0) : ℝ)
        ≤ (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) := by
      exact_mod_cast hSle
    linarith
  -- lacunarity: `Λ ^ n ≤ a n`
  have hpow : ((Λ : ℝ)) ^ n ≤ (a n : ℝ) := by
    have h := lowSmallSet_lacunary_pow_le ha ha1 n
    have h' : ((Λ ^ n : ℝ≥0) : ℝ) ≤ ((a n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr h
    rwa [NNReal.coe_pow] at h'
  have hlogS : (n : ℝ) * Real.log (Λ : ℝ)
      < Real.log ((Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) + 1) := by
    have h := Real.log_lt_log (pow_pos (by linarith : (0 : ℝ) < (Λ : ℝ)) n)
      (lt_of_le_of_lt hpow han)
    rwa [Real.log_pow] at h
  -- identify the split cut as `2 ^ (2 ^ U)`
  have hScast : (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ)
      = (2 : ℝ) ^ (2 ^ U) := by
    rw [hU, Work.KMTAreas.A7.uScale, Work.KMTAreas.A7.splitCut]
    push_cast
    ring
  -- `log (splitCut + 1) ≤ (2^U + 1) log 2`
  have hlogb : Real.log ((Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) + 1)
      ≤ ((2 : ℝ) ^ U + 1) * Real.log 2 := by
    have h1 : Real.log ((Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ) + 1)
        ≤ Real.log (2
            * (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      linarith
    have h2 : Real.log (2
          * (Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℝ))
        = Real.log 2 + (2 : ℝ) ^ U * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hSpos), hScast, Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    linarith
  have hn1 : (n : ℝ) * Real.log (Λ : ℝ) < ((2 : ℝ) ^ U + 1) * Real.log 2 :=
    lt_of_lt_of_le hlogS hlogb
  have hn2 : (n : ℝ) < ((2 : ℝ) ^ U + 1) * c := by
    have hdiv : (n : ℝ) < (((2 : ℝ) ^ U + 1) * Real.log 2) / Real.log (Λ : ℝ) := by
      rw [lt_div_iff₀ hlogΛ]
      exact hn1
    calc (n : ℝ) < (((2 : ℝ) ^ U + 1) * Real.log 2) / Real.log (Λ : ℝ) := hdiv
      _ = ((2 : ℝ) ^ U + 1) * c := by rw [hc]; ring
  -- the final arithmetic: `1 ≤ 2^U` buys the two extra powers of `2^U`
  have hq1 : (1 : ℝ) ≤ (2 : ℝ) ^ U := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hstep : ((2 : ℝ) ^ U + 1) * c + 1 ≤ (2 * c + 3) * (2 : ℝ) ^ U :=
    by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hq1)]
  have hmain : (n : ℝ) + 1 ≤ (2 * c + 3) * (2 : ℝ) ^ U := by linarith
  have hcoef : 2 * Real.log 2 / Real.log (Λ : ℝ) + 3 = 2 * c + 3 := by
    rw [hc]; ring
  rw [hcoef]
  exact hmain

end Work.KMTPlan.A6
