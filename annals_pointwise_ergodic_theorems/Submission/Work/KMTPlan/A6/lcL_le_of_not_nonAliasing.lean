import Mathlib
import Submission.Work.KMTPlan.A6.nonAliasing_of_size
import Submission.Work.KMTPlan.A6.two_mul_uScale_ge_rpow

namespace Work.KMTPlan.A6

open Real

/-- The scale count `uScale ρ L = ⌊2^{2ρL}⌋` dominates `2^{2ρL}/2`, i.e. the arc radius
`2^{-2·uScale ρ L}` is at most `2 · 2^{-2ρL}`: the scale `L` is at least `2ρL` *twice* in the
sense needed for the size comparison of the non-aliasing threshold.

This is the `uScale`-analogue of the arithmetic fact `x/2 ≤ ⌊x⌋` for `x ≥ 1`, written without the
`⌊·⌋` round trip. -/
theorem rpow_le_two_mul_uScale (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) :
    (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  set e : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with he
  have he1 : 1 ≤ e := by
    rw [he]
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by positivity)
  have hfloor_nn : (0 : ℤ) ≤ ⌊e⌋ := Int.floor_nonneg.mpr (by linarith)
  have hfloor_ge1 : (1 : ℝ) ≤ (⌊e⌋ : ℝ) := by
    have h1 : (1 : ℤ) ≤ ⌊e⌋ := by
      rw [Int.le_floor]
      exact_mod_cast he1
    exact_mod_cast h1
  have hfloor_lt : e - 1 < (⌊e⌋ : ℝ) := by
    have := Int.lt_floor_add_one e
    linarith
  have huScale : (Work.KMTAreas.A7.uScale ρ L : ℝ) = (⌊e⌋ : ℝ) := by
    have harg : ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) = e := by
      rw [he]; norm_num
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, harg]
    exact_mod_cast (Int.toNat_of_nonneg hfloor_nn)
  have hmain : e ≤ 2 * (⌊e⌋ : ℝ) := by linarith
  linarith [huScale ▸ hmain]

/-- **The non-aliasing threshold is at most logarithmic in the scale.**  If the good-major-arcs
condition `K + Cna · 2^{ρl} < 0` implies non-aliasing of the arithmetic frequencies
`(ℚ/ℤ)_{≤l}` (hypothesis `hsize`, a corollary of the Ionescu--Wainger Theorem `thm:iw`), then at
the scale `lcL l₁ l₂ k₁ k₂ = max(max l₁ l₂)(max k₁ k₂)` of the gain the arc radius
`2^{-2·uScale ρ (lcL ·)}` is *always* small enough for the union
`(ℚ/ℤ)_{≤l₁} ∪ (ℚ/ℤ)_{≤l₂}`, unless `lcL` is within `1 + log₂ Cna / ρ` of the origin.  In other
words: failure of non-aliasing forces `lcL ≤ ⌈logb 2 Cna / ρ⌉₊ + 1`, i.e. the scale is bounded by
a constant depending only on `ρ` and `Cna`. -/
theorem lcL_le_of_not_nonAliasing (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (Cna : ℝ) (hCna : 0 < Cna)
    (hsize : ∀ (l : ℕ) (K : ℤ),
      (K : ℝ) + Cna * (2 : ℝ) ^ (ρ * (l : ℝ)) < 0 →
        Work.Analysis.IonescuWainger.NonAliasing K (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    (l₁ l₂ k₁ k₂ : ℕ)
    (hna : ¬ Work.Analysis.IonescuWainger.NonAliasing
      (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)) :
    Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ ⌈Real.logb 2 Cna / ρ⌉₊ + 1 := by
  by_contra h
  rw [not_le] at h
  -- `lcL > ⌈logb 2 Cna / ρ⌉₊ + 1` gives `logb 2 Cna < ρ · lcL`.
  have hceil : ((⌈Real.logb 2 Cna / ρ⌉₊ : ℕ) : ℝ) < (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    have h1 : ((⌈Real.logb 2 Cna / ρ⌉₊ + 1 : ℕ) : ℝ) < ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h1
    linarith
  have hlog : Real.logb 2 Cna < ρ * (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    have h1 : Real.logb 2 Cna / ρ ≤ ((⌈Real.logb 2 Cna / ρ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : Real.logb 2 Cna / ρ < (lcL l₁ l₂ k₁ k₂ : ℝ) := lt_of_le_of_lt h1 hceil
    have h4 : ρ * (Real.logb 2 Cna / ρ) < ρ * (lcL l₁ l₂ k₁ k₂ : ℝ) :=
      mul_lt_mul_of_pos_left h3 hρ
    rwa [mul_div_cancel₀ (Real.logb 2 Cna) (ne_of_gt hρ)] at h4
  -- hence `Cna < 2^{ρ · lcL}`.
  have hCnaLt : Cna < (2 : ℝ) ^ (ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)) := by
    have hlogeq : (2 : ℝ) ^ Real.logb 2 Cna = Cna :=
      Real.rpow_logb (by norm_num) (by norm_num) hCna
    rw [← hlogeq]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hlog
  -- and `max l₁ l₂ ≤ lcL`, so `Cna · 2^{ρ·max l₁ l₂} < 2^{2ρ·lcL}`.
  have hMle : max l₁ l₂ ≤ lcL l₁ l₂ k₁ k₂ := le_max_left _ _
  have hMcast : ((max l₁ l₂ : ℕ) : ℝ) ≤ (lcL l₁ l₂ k₁ k₂ : ℝ) := by exact_mod_cast hMle
  have hMpow : (2:ℝ) ^ (ρ * ((max l₁ l₂ : ℕ) : ℝ))
      ≤ (2:ℝ) ^ (ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by nlinarith [hρ.le, hMcast])
  have hprod : Cna * (2:ℝ) ^ (ρ * ((max l₁ l₂ : ℕ) : ℝ))
      < (2:ℝ) ^ (2 * ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)) := by
    have hB : (0:ℝ) < (2:ℝ) ^ (ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hA : (0:ℝ) < (2:ℝ) ^ (ρ * ((max l₁ l₂ : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have step1 : Cna * (2:ℝ) ^ (ρ * ((max l₁ l₂ : ℕ) : ℝ))
        < (2:ℝ) ^ (ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)) * (2:ℝ) ^ (ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)) :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right hCnaLt hA) (mul_le_mul_of_nonneg_left hMpow hB.le)
    have hexp : ρ * (lcL l₁ l₂ k₁ k₂ : ℝ) + ρ * (lcL l₁ l₂ k₁ k₂ : ℝ)
        = 2 * ρ * (lcL l₁ l₂ k₁ k₂ : ℝ) := by ring
    rwa [← Real.rpow_add (show (0:ℝ) < 2 by norm_num), hexp] at step1
  -- `2 · uScale ρ lcL ≥ 2^{2ρ·lcL}` puts the size test in the good-major-arcs range.
  have hucount := rpow_le_two_mul_uScale ρ hρ.le (lcL l₁ l₂ k₁ k₂)
  have hunion := iwArithFreqs_union_max hρ hρ1 l₁ l₂
  refine hna ?_
  rw [hunion]
  exact hsize (max l₁ l₂)
    (-(2 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) : ℤ))
    (by
      push_cast
      rw [Nat.cast_max] at hprod
      linarith [hprod, hucount])

end Work.KMTPlan.A6
