import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log

namespace Work.KMTPlan.A6

open scoped NNReal

/-- The scale count `uScale ρ L = ⌊2^{2ρL}⌋` is monotone in `L`, for `ρ ≥ 0`. -/
private lemma uScale_mono (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Monotone (fun L : ℕ => Work.KMTAreas.A7.uScale ρ L) := by
  intro l l' hl
  simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat]
  apply Nat.floor_mono
  have hlR : (l : ℝ) ≤ (l' : ℝ) := by exact_mod_cast hl
  have hexp : 2 * ρ * (l : ℝ) ≤ 2 * ρ * (l' : ℝ) := by nlinarith
  have hpow : (2 : ℝ) ^ (2 * ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (l' : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- **Sharp count of the small-scale index set.**  A scale `N = ⌊a n⌋` that is admissible
(`inIndexSet`) and small (`N ≤ splitCut ρ L = 2^{2^u}`, `u = uScale ρ L = ⌊2^{2ρL}⌋`,
`L = lcL l₁ l₂ k₁ k₂`) forces `n + 1 ≲_Λ 2^u`, i.e. at most the (essentially sharp) number of
scales available below `splitCut`: the lacunarity gives `Λ^n ≤ a n < splitCut + 1` and hence
`n + 1 ≤ (log 2 / log Λ + 2) · 2^u` for all `L ≥ B`, with `B` depending only on `ρ` and `Λ`.

This strengthens `lowSmallSet_le_log`, whose right-hand side is `2^{2^u}` rather than `2^u`. -/
theorem lowSmallSet_le_log_sharp (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
      Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      (n : ℝ) + 1 ≤ (Real.log 2 / Real.log (Λ : ℝ) + 2)
        * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- (1) the threshold `m ≥ log 2 / log Λ`, and a level `B` with `⌊2^{2ρB}⌋ ≥ m`
  obtain ⟨m, hcm⟩ : ∃ m : ℕ, Real.log 2 / Real.log (Λ : ℝ) ≤ (m : ℝ) :=
    ⟨⌈Real.log 2 / Real.log (Λ : ℝ)⌉₊, Nat.le_ceil _⟩
  obtain ⟨B, hmB⟩ : ∃ B : ℕ, (m : ℝ) ≤ 2 * ρ * (B : ℝ) := by
    refine ⟨⌈(m : ℝ) / (2 * ρ)⌉₊, ?_⟩
    have h1 : (m : ℝ) / (2 * ρ) ≤ ((⌈(m : ℝ) / (2 * ρ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) < 2 * ρ := by linarith
    have h3 : (m : ℝ) ≤ ((⌈(m : ℝ) / (2 * ρ)⌉₊ : ℕ) : ℝ) * (2 * ρ) :=
      (div_le_iff₀ h2).mp h1
    linarith
  have huB : m ≤ Work.KMTAreas.A7.uScale ρ B := by
    rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat]
    apply Nat.le_floor
    have hm2 : (m : ℝ) ≤ (2 : ℝ) ^ (m : ℝ) := by
      have h : (m : ℝ) ≤ ((2 : ℕ) ^ m : ℝ) := by
        exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := m)))
      simpa using h
    have hstep : (2 : ℝ) ^ (m : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (B : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hmB
    simpa using le_trans hm2 hstep
  refine ⟨B, ?_⟩
  intro a l₁ l₂ k₁ k₂ n ha ha1 hB hsm
  obtain ⟨_, hsmLe⟩ := hsm
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hLdef
  set c : ℝ := Real.log 2 / Real.log (Λ : ℝ) with hcdef
  set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hudef
  have hc0 : 0 ≤ c := by rw [hcdef]; exact div_nonneg (le_of_lt hlog2) (le_of_lt hlogΛ)
  -- (2) `c ≤ u` for every scale `L ≥ B`
  have hcu : c ≤ (u : ℝ) := by
    have hmono : Work.KMTAreas.A7.uScale ρ B ≤ Work.KMTAreas.A7.uScale ρ L :=
      uScale_mono ρ (le_of_lt hρ) hB
    have hmu : m ≤ u := by
      rw [hudef]
      exact le_trans huB hmono
    have hmuc : (m : ℝ) ≤ (u : ℝ) := by exact_mod_cast hmu
    linarith
  -- (3) `Nat.floor (a n) ≤ splitCut ρ L` and `a n < splitCut ρ L + 1`
  have hSle : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ L := by
    simpa only [hLdef] using hsmLe
  have hS1 : 1 ≤ Work.KMTAreas.A7.splitCut ρ L := by
    rw [Work.KMTAreas.A7.splitCut]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hSpos : (0 : ℝ) < (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS1)
  have han : (a n : ℝ) < (Work.KMTAreas.A7.splitCut ρ L : ℝ) + 1 := by
    have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℝ≥0) : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (a n)
    have h2 : ((Nat.floor (a n) : ℝ≥0) : ℝ) ≤ (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
      exact_mod_cast hSle
    linarith
  -- (4) lacunarity: `Λ^n ≤ a n`, hence `n log Λ < log (splitCut + 1)`
  have hpow : ((Λ : ℝ)) ^ n ≤ (a n : ℝ) := by
    have h := lowSmallSet_lacunary_pow_le ha ha1 n
    have h' : ((Λ ^ n : ℝ≥0) : ℝ) ≤ ((a n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr h
    rwa [NNReal.coe_pow] at h'
  have hlogS : (n : ℝ) * Real.log (Λ : ℝ) <
      Real.log ((Work.KMTAreas.A7.splitCut ρ L : ℝ) + 1) := by
    have h := Real.log_lt_log (pow_pos (by linarith : (0 : ℝ) < (Λ : ℝ)) n)
      (lt_of_le_of_lt hpow han)
    rwa [Real.log_pow] at h
  -- (5) `log (splitCut + 1) ≤ (2^u + 1) log 2`
  have hScast : (Work.KMTAreas.A7.splitCut ρ L : ℝ) = (2 : ℝ) ^ (2 ^ u) := by
    rw [hudef, Work.KMTAreas.A7.uScale, Work.KMTAreas.A7.splitCut]
    push_cast
    ring
  have hS1R : (1 : ℝ) ≤ (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
    exact_mod_cast hS1
  have hlogb : Real.log ((Work.KMTAreas.A7.splitCut ρ L : ℝ) + 1) ≤
      ((2 : ℝ) ^ u + 1) * Real.log 2 := by
    have h1 : Real.log ((Work.KMTAreas.A7.splitCut ρ L : ℝ) + 1) ≤
        Real.log (2 * (Work.KMTAreas.A7.splitCut ρ L : ℝ)) := by
      apply Real.log_le_log (by positivity)
      linarith
    have h2 : Real.log (2 * (Work.KMTAreas.A7.splitCut ρ L : ℝ)) =
        Real.log 2 + (2 : ℝ) ^ u * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hSpos), hScast, Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    linarith
  -- (6) divide by `log Λ > 0`
  have hn1 : (n : ℝ) * Real.log (Λ : ℝ) < ((2 : ℝ) ^ u + 1) * Real.log 2 :=
    lt_of_lt_of_le hlogS hlogb
  have hn2 : (n : ℝ) < ((2 : ℝ) ^ u + 1) * c := by
    have hdiv : (n : ℝ) < (((2 : ℝ) ^ u + 1) * Real.log 2) / Real.log (Λ : ℝ) := by
      rw [lt_div_iff₀ hlogΛ]
      exact hn1
    calc (n : ℝ) < (((2 : ℝ) ^ u + 1) * Real.log 2) / Real.log (Λ : ℝ) := hdiv
      _ = ((2 : ℝ) ^ u + 1) * c := by rw [hcdef]; ring
  -- (7) the arithmetic conclusion: `c + 1 ≤ 2^{u+1}`
  have hu2 : c + 1 ≤ 2 * (2 : ℝ) ^ u := by
    have hnat : u + 1 ≤ (2 : ℕ) ^ (u + 1) := le_of_lt (Nat.lt_two_pow_self (n := u + 1))
    have hreal : (u : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ u := by
      calc (u : ℝ) + 1 = ((u + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (((2 : ℕ) ^ (u + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 2 * (2 : ℝ) ^ u := by push_cast; rw [pow_succ]; ring
    linarith
  have hmain : (n : ℝ) + 1 ≤ (c + 2) * (2 : ℝ) ^ u := by
    have h : ((2 : ℝ) ^ u + 1) * c + 1 ≤ (c + 2) * (2 : ℝ) ^ u := by nlinarith [hu2]
    linarith [hn2, h]
  exact hmain

end Work.KMTPlan.A6
