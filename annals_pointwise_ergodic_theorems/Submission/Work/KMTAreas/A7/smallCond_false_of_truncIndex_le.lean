/-
# The small-scale condition fails beyond the truncation index

The §7 small-scale tuple of area `A7` is cut off at the index
`truncIndex ρ Λ (smallL l₁ l₂ k₁ k₂)` (`SmallModelDefs.truncIndex`), because beyond it the
small-scale condition `smallCond` is *never* satisfied: `smallCond` requires
`⌊a n⌋ ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂)`, while the lacunarity forces the scales to grow at
least geometrically, `a n ≥ Λ ^ n`, and the truncation index is chosen precisely so that
`Λ ^ truncIndex > splitCut ρ L + 1`.

This module proves that elementary implication.

## The two estimates

* `Work.KMTAreas.A7.lacunary_pow_le` (from `ExcAux`) : `Λ ^ n ≤ a n` for a `Λ`-lacunary sequence
  with `a n ≥ 1`.
* `splitCut_add_one_le_pow_truncIndex` : `(splitCut ρ L : ℝ) + 1 ≤ Λ ^ truncIndex ρ Λ L`.

The second is the content of the definition of the truncation index:
with `c = ⌈log (splitCut ρ L + 1) / log Λ⌉` one has `log (splitCut ρ L + 1) ≤ c · log Λ`, hence
`splitCut ρ L + 1 ≤ Λ ^ c` after exponentiation, and then
`Λ ^ (c + 2) = Λ ^ c · Λ ^ 2 > splitCut ρ L + 1` because `Λ ^ 2 > 1`.  (The extra factor `Λ ^ 2`
in the truncation index is what makes the inequality *strict* where it needs to be: it turns
`⌊a n⌋ ≥ splitCut ρ L` into `⌊a n⌋ > splitCut ρ L`.)
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.ExcAux

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped NNReal

/-- The defining property of the truncation index: below the index
`truncIndex ρ Λ L = ⌈log (splitCut ρ L + 1) / log Λ⌉ + 2` the small scales have already been left,
`(splitCut ρ L : ℝ) + 1 ≤ Λ ^ truncIndex ρ Λ L`. -/
private theorem splitCut_add_one_le_pow_truncIndex (ρ : ℝ) (Λ : NNReal) (L : ℕ)
    (hΛ : 1 < Λ) : ((splitCut ρ L : ℝ) + 1) ≤ (Λ : ℝ) ^ (truncIndex ρ Λ L) := by
  have hΛ1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by linarith
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛ1
  have hSp1 : (0 : ℝ) < (splitCut ρ L : ℝ) + 1 := by positivity
  set c : ℕ := Nat.ceil (Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ : ℝ)) with hc
  -- `log (splitCut ρ L + 1) ≤ c log Λ`
  have hlog_le : Real.log ((splitCut ρ L : ℝ) + 1) ≤ (c : ℝ) * Real.log (Λ : ℝ) := by
    have h := Nat.le_ceil (Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ : ℝ))
    have h2 := mul_le_mul_of_nonneg_right h hlogΛ.le
    rw [div_mul_cancel₀ _ hlogΛ.ne'] at h2
    exact h2
  -- hence `splitCut ρ L + 1 ≤ Λ ^ c`
  have hpowc : (splitCut ρ L : ℝ) + 1 ≤ (Λ : ℝ) ^ c := by
    have h1 := (Real.log_le_iff_le_exp hSp1).mp hlog_le
    rw [Real.exp_nat_mul, Real.exp_log hΛpos] at h1
    exact h1
  -- and `Λ ^ (c + 2) = Λ ^ c * Λ ^ 2 > splitCut ρ L + 1`
  have hT : truncIndex ρ Λ L = c + 2 := by rw [hc]; rfl
  rw [hT, pow_add]
  have h2 : (1 : ℝ) < (Λ : ℝ) ^ 2 := by nlinarith
  have hposc : (0 : ℝ) < (Λ : ℝ) ^ c := lt_of_lt_of_le hSp1 hpowc
  calc (splitCut ρ L : ℝ) + 1 = ((splitCut ρ L : ℝ) + 1) * 1 := by ring
    _ ≤ (Λ : ℝ) ^ c * (Λ : ℝ) ^ 2 := mul_le_mul hpowc h2.le (by norm_num) hposc.le

theorem smallCond_false_of_truncIndex_le (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) (hΛ : 1 < Λ) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
    (ha1 : ∀ m, 1 ≤ a m)
    (hn : Work.KMTAreas.A7.truncIndex ρ Λ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) ≤ n) :
    ¬ Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n := by
  intro hcond
  -- `smallCond` forces the scale to be small, `⌊a n⌋ ≤ splitCut ρ L`
  have hSle : Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) := hcond.2.1
  have hΛ1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  -- lacunarity and `hn : truncIndex ≤ n` give `Λ ^ truncIndex ≤ a n`
  have hgrowth : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    exact_mod_cast (lacunary_pow_le (Λ := Λ) (a := a) ha ha1 n)
  have hmono : (Λ : ℝ) ^ (truncIndex ρ Λ (smallL l₁ l₂ k₁ k₂)) ≤ (Λ : ℝ) ^ n :=
    pow_le_pow_right₀ hΛ1.le hn
  have hpow : (Λ : ℝ) ^ (truncIndex ρ Λ (smallL l₁ l₂ k₁ k₂)) ≤ (a n : ℝ) :=
    le_trans hmono hgrowth
  have hcut := splitCut_add_one_le_pow_truncIndex ρ Λ (smallL l₁ l₂ k₁ k₂) hΛ
  -- hence `splitCut ρ L + 1 ≤ ⌊a n⌋`, contradicting `⌊a n⌋ ≤ splitCut ρ L`
  have hbig : (splitCut ρ (smallL l₁ l₂ k₁ k₂) : ℝ) + 1 ≤ (a n : ℝ) := le_trans hcut hpow
  have hbigNN : (((splitCut ρ (smallL l₁ l₂ k₁ k₂) + 1 : ℕ)) : ℝ≥0) ≤ a n := by
    exact_mod_cast hbig
  have hfloor : splitCut ρ (smallL l₁ l₂ k₁ k₂) + 1 ≤ Nat.floor (a n) := Nat.le_floor hbigNN
  omega

end Work.KMTAreas.A7
