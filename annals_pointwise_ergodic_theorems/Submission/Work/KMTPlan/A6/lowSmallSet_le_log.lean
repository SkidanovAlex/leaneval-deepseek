import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs

namespace Work.KMTPlan.A6

open scoped NNReal

/-- **Growth of a lacunary sequence.**  A `Λ`-lacunary sequence bounded below by `1` grows at
least geometrically: `Λ ^ n ≤ a n` for every `n`. -/
theorem lowSmallSet_lacunary_pow_le {Λ : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) :
    Λ ^ n ≤ a n := by
  induction n with
  | zero => simpa using ha1 0
  | succ k ih =>
      have hpos : (0 : ℝ≥0) < a k := lt_of_lt_of_le zero_lt_one (ha1 k)
      have hstep : Λ * a k ≤ a (k + 1) := le_of_lt ((lt_div_iff₀ hpos).mp (ha k))
      calc Λ ^ (k + 1) = Λ * Λ ^ k := pow_succ' Λ k
        _ ≤ Λ * a k := mul_le_mul_of_nonneg_left ih bot_le
        _ ≤ a (k + 1) := hstep

/-- **The elementary logarithmic bound.**  For `Λ > 1` and `S ≥ 1`,
`log (S + 1) / log Λ + 1 ≤ ((log 2 + 1) / log Λ + 1) · S`. -/
theorem lowSmallSet_log_bound {Λ S : ℝ} (hΛ : 1 < Λ) (hS : 1 ≤ S) :
    Real.log (S + 1) / Real.log Λ + 1 ≤ ((Real.log 2 + 1) / Real.log Λ + 1) * S := by
  have hc : 0 < Real.log Λ := Real.log_pos hΛ
  have hcne : Real.log Λ ≠ 0 := ne_of_gt hc
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  -- `log (S+1) ≤ log 2 + S - 1`
  have hlog_le : Real.log (S + 1) ≤ Real.log 2 + S - 1 := by
    have hmono : Real.log (S + 1) ≤ Real.log (2 * S) := by
      apply Real.log_le_log (by linarith)
      linarith
    have hmul : Real.log (2 * S) = Real.log 2 + Real.log S :=
      Real.log_mul (by norm_num) (ne_of_gt hSpos)
    have hle : Real.log S ≤ S - 1 := Real.log_le_sub_one_of_pos hSpos
    rw [hmul] at hmono
    linarith
  have key : Real.log (S + 1) + Real.log Λ ≤ (Real.log 2 + 1 + Real.log Λ) * S := by
    have h1 : 0 ≤ Real.log 2 * (S - 1) := mul_nonneg hlog2 (by linarith)
    have h2 : 0 ≤ Real.log Λ * (S - 1) := mul_nonneg (le_of_lt hc) (by linarith)
    nlinarith [hlog_le, h1, h2]
  have key2 : (Real.log (S + 1) + Real.log Λ) / Real.log Λ
      ≤ ((Real.log 2 + 1 + Real.log Λ) * S) / Real.log Λ :=
    div_le_div_of_nonneg_right key (le_of_lt hc)
  have e1 : (Real.log (S + 1) + Real.log Λ) / Real.log Λ
      = Real.log (S + 1) / Real.log Λ + 1 := by
    rw [add_div, div_self hcne]
  have e2 : ((Real.log 2 + 1 + Real.log Λ) * S) / Real.log Λ
      = ((Real.log 2 + 1) / Real.log Λ + 1) * S := by
    calc ((Real.log 2 + 1 + Real.log Λ) * S) / Real.log Λ
        = ((Real.log 2 + 1 + Real.log Λ) / Real.log Λ) * S := by ring
      _ = ((Real.log 2 + 1) / Real.log Λ + 1) * S := by rw [add_div, div_self hcne]
  rw [e1, e2] at key2
  exact key2

open MeasureTheory in
open scoped ENNReal NNReal BigOperators in
/-- **The count of the small-scale index set.**  A scale `N = ⌊a n⌋` that is admissible
(`inIndexSet`) and small (`N ≤ splitCut ρ L`) forces `n` to be at most
`D(Λ) · 2^{2^{scaleCount 1 ρ L}}`: the lacunarity `Λ^n ≤ a n` gives `n ≲ log_Λ(2 · splitCut ρ L)`,
and the constant may depend on `Λ`. -/
theorem lowSmallSet_le_log (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    ∃ D : ℝ≥0 → ℝ, (∀ Λ : ℝ≥0, 1 < Λ → 0 < D Λ) ∧
      ∀ Λ : ℝ≥0, 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
          (n : ℝ) + 1 ≤ D Λ * (2 : ℝ) ^ (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ
            (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) := by
  refine ⟨fun Λ => (Real.log 2 + 1) / Real.log ((Λ : ℝ)) + 1, ?_, ?_⟩
  · intro Λ hΛ
    have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hc : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
    have hnum : 0 < Real.log 2 + 1 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    have hq : 0 < (Real.log 2 + 1) / Real.log (Λ : ℝ) := div_pos hnum hc
    linarith
  · intro Λ hΛ ha ha1 hsm
    have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hc : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
    have hΛpos : (0 : ℝ) < (Λ : ℝ) := by linarith
    obtain ⟨-, hle⟩ := hsm
    set S : ℕ := Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) with hSdef
    have hle' : Nat.floor (a n) ≤ S := hle
    have hS1 : 1 ≤ S := by
      rw [hSdef, Work.KMTAreas.A7.splitCut]
      exact Nat.one_le_pow _ _ (by norm_num)
    have hS1R : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
    -- `a n < S + 1`
    have han : (a n : ℝ) < (S : ℝ) + 1 := by
      have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℝ≥0) : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one (a n)
      have h2 : ((Nat.floor (a n) : ℝ≥0) : ℝ) ≤ (S : ℝ) := by
        exact_mod_cast hle'
      linarith
    -- lacunary growth
    have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
      have h := lowSmallSet_lacunary_pow_le ha ha1 n
      have h' : ((Λ ^ n : ℝ≥0) : ℝ) ≤ ((a n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr h
      rwa [NNReal.coe_pow] at h'
    have hlog : (n : ℝ) * Real.log (Λ : ℝ) ≤ Real.log ((S : ℝ) + 1) := by
      have hlt : (Λ : ℝ) ^ n < (S : ℝ) + 1 := lt_of_le_of_lt hpow han
      have h := Real.log_le_log (pow_pos hΛpos n) (le_of_lt hlt)
      rwa [Real.log_pow] at h
    have hnbd : (n : ℝ) ≤ Real.log ((S : ℝ) + 1) / Real.log (Λ : ℝ) :=
      (le_div_iff₀ hc).mpr hlog
    have hmain := lowSmallSet_log_bound hΛR hS1R
    have hfinal : (n : ℝ) + 1
        ≤ ((Real.log 2 + 1) / Real.log (Λ : ℝ) + 1) * (S : ℝ) := by linarith
    have hSe : ((S : ℕ) : ℝ)
        = (2 : ℝ) ^ (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ
            (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) := by
      rw [hSdef, Work.KMTAreas.A7.splitCut]
      push_cast
      rfl
    rwa [hSe] at hfinal

end Work.KMTPlan.A6
