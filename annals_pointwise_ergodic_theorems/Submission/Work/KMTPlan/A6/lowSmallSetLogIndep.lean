import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log

namespace Work.KMTPlan.A6

open scoped NNReal

/-- **The arithmetic core of `lowSmallSetLogIndep`.**  If `Λ > 1` and
`n · log Λ ≤ (1 + 2^u) · log 2`, then `n + 1 ≤ (2 log 2 / log Λ + 3) · 2^u`.

Indeed, dividing by `log Λ` gives `n ≤ (1 + 2^u) c`, `c = log 2 / log Λ ≥ 0`; with `2^u ≥ 1` we
have `c + 1 ≤ (c + 3) · 2^u`, and adding the two inequalities yields
`n + 1 ≤ (2c + 3) · 2^u`. -/
private lemma logIndepArith {Λ : ℝ} (hΛ : 1 < Λ) {n u : ℕ}
    (hn : (n : ℝ) * Real.log Λ ≤ (1 + (2 : ℝ) ^ u) * Real.log 2) :
    (n : ℝ) + 1 ≤ (2 * Real.log 2 / Real.log Λ + 3) * (2 : ℝ) ^ u := by
  have hlogΛ : 0 < Real.log Λ := Real.log_pos hΛ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 / Real.log Λ with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; exact div_nonneg (le_of_lt hlog2) (le_of_lt hlogΛ)
  have hdiv : (n : ℝ) ≤ (1 + (2 : ℝ) ^ u) * c := by
    have h := (le_div_iff₀ hlogΛ).mpr hn
    rwa [mul_div_assoc, ← hcdef] at h
  have hP1 : (1 : ℝ) ≤ (2 : ℝ) ^ u := one_le_pow₀ (by norm_num)
  have hstep : c + 1 ≤ (c + 3) * (2 : ℝ) ^ u := by
    have h := mul_le_mul_of_nonneg_left hP1 (by linarith : (0 : ℝ) ≤ c + 3)
    linarith
  have hcoef : 2 * Real.log 2 / Real.log Λ + 3 = 2 * c + 3 := by
    rw [hcdef]; ring
  rw [hcoef]
  nlinarith [hdiv, hstep, hc0, hP1]

theorem lowSmallSetLogIndep (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
    (hΛ : 1 < Λ) (hlac : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ n : ℕ) (h : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (n : ℝ) + 1 ≤ (2 * Real.log 2 / Real.log (Λ : ℝ) + 3)
      * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := lt_trans zero_lt_one hΛR
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hLdef
  set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hudef
  -- the scale `⌊a n⌋` is admissible and small: `⌊a n⌋ ≤ splitCut ρ L = 2 ^ 2 ^ u`
  have hSle : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ L := by
    obtain ⟨-, h2⟩ := h
    simpa only [hLdef] using h2
  have hS1 : 1 ≤ Work.KMTAreas.A7.splitCut ρ L := by
    rw [Work.KMTAreas.A7.splitCut]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hScast : (Work.KMTAreas.A7.splitCut ρ L : ℝ) = (2 : ℝ) ^ (2 ^ u) := by
    rw [hudef, Work.KMTAreas.A7.uScale, Work.KMTAreas.A7.splitCut]
    push_cast
    ring
  have hSpos : (0 : ℝ) < (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
    rw [hScast]; positivity
  -- `a n < splitCut + 1 ≤ 2 · splitCut`
  have han : (a n : ℝ) < 2 * (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
    have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℝ≥0) : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (a n)
    have h2 : ((Nat.floor (a n) : ℝ≥0) : ℝ) ≤ (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
      exact_mod_cast hSle
    have h3 : (1 : ℝ) ≤ (Work.KMTAreas.A7.splitCut ρ L : ℝ) := by
      exact_mod_cast hS1
    linarith
  -- lacunarity: `Λ ^ n ≤ a n`
  have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    have h' := lowSmallSet_lacunary_pow_le hlac ha1 n
    have h'' : ((Λ ^ n : ℝ≥0) : ℝ) ≤ ((a n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr h'
    rwa [NNReal.coe_pow] at h''
  have hlog : (n : ℝ) * Real.log (Λ : ℝ)
      ≤ Real.log (2 * (Work.KMTAreas.A7.splitCut ρ L : ℝ)) := by
    have hlt : (Λ : ℝ) ^ n < 2 * (Work.KMTAreas.A7.splitCut ρ L : ℝ) :=
      lt_of_le_of_lt hpow han
    have h := Real.log_le_log (pow_pos hΛpos n) (le_of_lt hlt)
    rwa [Real.log_pow] at h
  have hlogS : Real.log (2 * (Work.KMTAreas.A7.splitCut ρ L : ℝ))
      = (1 + (2 : ℝ) ^ u) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hSpos), hScast, Real.log_pow]
    push_cast
    ring
  have hn : (n : ℝ) * Real.log (Λ : ℝ) ≤ (1 + (2 : ℝ) ^ u) * Real.log 2 := by
    rw [hlogS] at hlog; exact hlog
  have hmain := logIndepArith hΛR hn
  simpa only [hudef, hLdef] using hmain

end Work.KMTPlan.A6
