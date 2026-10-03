/-
# Absorption of the truncation index into the loss weight (KMT, area A7)

The Rademacher--Menshov truncation of the small-scale model tuple of §7 is taken at the index
`truncIndex ρ Λ L` (`L = max (max l₁ l₂) (max k₁ k₂)`); the two-dimensional RM inequality then
costs a factor `(log₂ (truncIndex + 1) + 2)²`, which has to be absorbed into the loss weight
`⟨L⟩^{A+4} 2^{(A+4)ρL}` of the small-scale estimate.  This module proves that absorption.

## The mathematics

Write `n = scaleCount 1 ρ L = ⌊2^{2ρL}⌋` and `s = splitCut ρ L = 2^{2ⁿ}`, so that
`truncIndex ρ Λ L = ⌈log (s+1) / log Λ⌉ + 2`.

* `log (s+1) ≤ (1 + 2ⁿ) log 2`, because `s ≥ 1` gives `s + 1 ≤ 2s` and `log s = 2ⁿ log 2`.
* If `log Λ ≤ 0` then the ceiling index is `0` and `truncIndex = 2`, so the RM cost is `(1+2)² = 9`.
* If `log Λ > 0` then, with `d = log₂ / log Λ = Real.logb Λ 2 > 0`,
  `truncIndex ≤ (1 + 2ⁿ) d + 3 ≤ 2^{n+1} (d + 4)` (using `2ⁿ ≥ 1`), hence
  `log₂ (truncIndex + 1) ≤ (n + 1) + log₂ (d + 4)`.

In both cases `log₂ (truncIndex + 1) + 2 ≤ n + c(Λ)` with
`c(Λ) = 5 + log₂ (max 0 (logb Λ 2) + 4) ≥ 7`, which is *independent of `ρ`, `A` and `L`* except
through `n = scaleCount 1 ρ L`.  Since `n ≤ 2^{2ρL} =: e`, the RM cost is bounded by
`(e + c(Λ))²`, and the elementary bound `(e + c)² ≤ 4c² · W · e²` (valid for `c, e ≥ 1`,
`W = ⟨L⟩⁴ ≥ 1`) shows that it is absorbed by the factor `⟨L⟩⁴ 2^{4ρL}` present in
`lossWeight (A+4) ρ l₁ l₂ k₁ k₂` but not in `lossWeight A ρ l₁ l₂ k₁ k₂`.

The constant `S Λ = 4 c(Λ)²` is therefore finite for every `Λ` (note that `Λ` is arbitrary:
`Λ ≤ 1` only makes `c` smaller), and the absorption holds uniformly in `ρ > 0`, `A ≥ 0` and the
scales `l₁, l₂, k₁, k₂`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.scaleCount_le_rpow
import Submission.Work.KMTAreas.A7.lossAbsorb_algebra
import Submission.Work.KMTAreas.A7.sq_add_le_four_mul

namespace Work.KMTAreas.A7

noncomputable section

/-- `d(Λ) = log₂ / log Λ = logb Λ 2`, clamped below at `0`.  It is the only place where the
lacunarity parameter `Λ` enters the bound for the truncation index. -/
noncomputable def absorbD (Λ : NNReal) : ℝ := max 0 (Real.logb (Λ : ℝ) 2)

/-- `c(Λ) = 5 + log₂ (d(Λ) + 4) ≥ 7`.  It bounds `log₂ (truncIndex ρ Λ L + 1) + 2 - n` uniformly
in `ρ`, `A` and `L`, where `n = scaleCount 1 ρ L`. -/
noncomputable def absorbC (Λ : NNReal) : ℝ := 5 + Real.logb 2 (absorbD Λ + 4)

/-- The constant `S Λ = 4 c(Λ)²` of the absorption. -/
noncomputable def absorbS (Λ : NNReal) : ℝ := 4 * absorbC Λ ^ 2

theorem absorbD_nonneg (Λ : NNReal) : 0 ≤ absorbD Λ := le_max_left _ _

theorem absorbC_ge_seven (Λ : NNReal) : 7 ≤ absorbC Λ := by
  unfold absorbC absorbD
  have h : (4:ℝ) ≤ max 0 (Real.logb (↑Λ) 2) + 4 := by
    have := le_max_left (0:ℝ) (Real.logb (↑Λ) 2); linarith
  have h2 : Real.logb 2 (4:ℝ) ≤ Real.logb 2 (max 0 (Real.logb (↑Λ) 2) + 4) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h
  have h3 : Real.logb 2 (4:ℝ) = 2 := by
    have h4 : (4:ℝ) = (2:ℝ)^2 := by norm_num
    rw [h4, Real.logb_pow]
    norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  linarith

theorem absorbC_pos (Λ : NNReal) : 0 < absorbC Λ := lt_of_lt_of_le (by norm_num) (absorbC_ge_seven Λ)

theorem absorbS_pos (Λ : NNReal) : 0 < absorbS Λ := by
  unfold absorbS
  have h := absorbC_ge_seven Λ
  nlinarith

/-- `scaleCount 1 ρ L = ⌊2^{2ρL}⌋ ≤ 2^{2ρL}`. -/
theorem scaleCount_le_two_rpow (ρ : ℝ) (L : ℕ) :
    (Work.Analysis.EndVar.scaleCount 1 ρ L : ℝ) ≤ (2:ℝ) ^ (2 * ρ * (L:ℝ)) := by
  unfold Work.Analysis.EndVar.scaleCount
  simpa only [Int.floor_toNat, Nat.cast_one, one_mul]
    using Nat.floor_le (show (0:ℝ) ≤ 1 * 2 ^ (2 * ρ * (L:ℝ)) by positivity)

/-- `splitCut ρ L = 2^{2ⁿ}` with `n = scaleCount 1 ρ L`, as a real number. -/
theorem splitCut_cast (ρ : ℝ) (L : ℕ) (n : ℕ) (hn : n = Work.Analysis.EndVar.scaleCount 1 ρ L) :
    (splitCut ρ L : ℝ) = (2:ℝ) ^ (2 ^ n) := by
  subst hn
  simp only [splitCut, Nat.cast_pow, Nat.cast_ofNat]

/-- **The truncation index is absorbed by the scale count.**  For every `ρ > 0`, `Λ` and `L`,
`log₂ (truncIndex ρ Λ L + 1) + 2 ≤ scaleCount 1 ρ L + c(Λ)`. -/
theorem truncIndex_log2_add_two_le (ρ : ℝ) (hρ : 0 < ρ) (Λ : NNReal) (L : ℕ) :
    ((Nat.log2 (truncIndex ρ Λ L + 1) : ℝ) + 2) ≤
      (Work.Analysis.EndVar.scaleCount 1 ρ L : ℝ) + absorbC Λ := by
  obtain ⟨n, hn⟩ : ∃ n, n = Work.Analysis.EndVar.scaleCount 1 ρ L := ⟨_, rfl⟩
  -- (A) `log (splitCut + 1) ≤ (1 + 2^n) log 2`
  have hsplit : (splitCut ρ L : ℝ) = (2 : ℝ) ^ (2 ^ n) := splitCut_cast ρ L n hn
  have hX1 : (1:ℝ) ≤ (splitCut ρ L : ℝ) := by
    rw [hsplit]; exact one_le_pow₀ (by norm_num)
  have hXpos : 0 < (splitCut ρ L : ℝ) := lt_of_lt_of_le zero_lt_one hX1
  have hA : Real.log ((splitCut ρ L : ℝ) + 1) ≤ (1 + (2:ℝ)^n) * Real.log 2 := by
    have h1 : Real.log ((splitCut ρ L : ℝ) + 1) ≤ Real.log (2 * (splitCut ρ L : ℝ)) := by
      apply Real.log_le_log (by positivity)
      linarith
    have h2 : Real.log (2 * (splitCut ρ L : ℝ)) = Real.log 2 + Real.log (splitCut ρ L : ℝ) :=
      Real.log_mul (by norm_num) hXpos.ne'
    have h3 : Real.log (splitCut ρ L : ℝ) = ((2:ℝ)^n) * Real.log 2 := by
      rw [hsplit, Real.log_pow]
      push_cast
      ring
    rw [h2, h3] at h1
    nlinarith [h1]
  -- (B) `Nat.log2 m ≤ logb 2 m`
  have hB : ((Nat.log2 (truncIndex ρ Λ L + 1) : ℝ)) ≤
      Real.logb 2 ((truncIndex ρ Λ L : ℝ) + 1) := by
    rw [Nat.log2_eq_log_two]
    have h := Real.natLog_le_logb (truncIndex ρ Λ L + 1) 2
    simpa using h
  by_cases hlog : Real.log (Λ : ℝ) ≤ 0
  · -- Case `log Λ ≤ 0`: the ceiling index vanishes and `truncIndex = 2`.
    have hnum : 0 ≤ Real.log ((splitCut ρ L : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hx : Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ : ℝ) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hnum hlog
    have hu : truncIndex ρ Λ L = 2 := by
      unfold truncIndex
      rw [Nat.ceil_eq_zero.mpr hx]
    have h3 : (Nat.log2 (truncIndex ρ Λ L + 1) : ℝ) ≤ 3 := by
      have hu' : truncIndex ρ Λ L + 1 = 3 := by omega
      rw [hu']
      have h31 : Nat.log2 3 = 1 := by decide
      simp [h31]
    have h7 := absorbC_ge_seven Λ
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  · -- Case `log Λ > 0`.
    push_neg at hlog
    have hdpos : 0 < Real.logb (Λ:ℝ) 2 := by
      simp only [Real.logb]
      exact div_pos (Real.log_pos (by norm_num)) hlog
    have hD : absorbD Λ = Real.logb (Λ:ℝ) 2 := max_eq_right (le_of_lt hdpos)
    have hxle : Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ:ℝ) ≤
        (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 := by
      have h1 : ((1 + (2:ℝ)^n) * Real.log 2) / Real.log (Λ:ℝ) =
          (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 := by
        rw [mul_div_assoc]; rfl
      calc Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ:ℝ)
          ≤ ((1 + (2:ℝ)^n) * Real.log 2) / Real.log (Λ:ℝ) :=
            div_le_div_of_nonneg_right hA (le_of_lt hlog)
        _ = (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 := h1
    have hceil : Nat.ceil (Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ:ℝ))
        ≤ Nat.ceil ((1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2) := by
      apply Nat.ceil_le.mpr
      calc Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ:ℝ)
          ≤ (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 := hxle
        _ ≤ (Nat.ceil ((1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2) : ℝ) := Nat.le_ceil _
    have hy0 : 0 ≤ (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 := by positivity
    have hceil2 : (Nat.ceil ((1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2) : ℝ)
        ≤ (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 + 1 := le_of_lt (Nat.ceil_lt_add_one hy0)
    have hu : (truncIndex ρ Λ L : ℝ) ≤ (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 + 3 := by
      unfold truncIndex
      push_cast
      have hcast : (Nat.ceil (Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ:ℝ)) : ℝ)
          ≤ (Nat.ceil ((1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2) : ℝ) := Nat.cast_le.mpr hceil
      linarith
    have h2n1 : (1:ℝ) + (2:ℝ)^n ≤ (2:ℝ)^(n+1) := by
      rw [pow_succ]; nlinarith [one_le_pow₀ (a := (2:ℝ)) (by norm_num) (n := n)]
    have hu1 : (truncIndex ρ Λ L : ℝ) + 1 ≤ (2:ℝ)^(n+1) * (Real.logb (Λ:ℝ) 2 + 4) := by
      have hprod : (1 + (2:ℝ)^n) * Real.logb (Λ:ℝ) 2 ≤ (2:ℝ)^(n+1) * Real.logb (Λ:ℝ) 2 :=
        mul_le_mul_of_nonneg_right h2n1 (le_of_lt hdpos)
      have hge1 : (1:ℝ) ≤ (2:ℝ)^(n+1) := by
        have h0 : (0:ℝ) ≤ (2:ℝ)^n := by positivity
        linarith [h2n1]
      have h4 : (4:ℝ) ≤ (2:ℝ)^(n+1) * 4 := by nlinarith [hge1]
      nlinarith [hu, hprod, h4]
    have hpos2 : 0 < (2:ℝ)^(n+1) * (Real.logb (Λ:ℝ) 2 + 4) := by positivity
    have hlogm : Real.logb 2 ((truncIndex ρ Λ L : ℝ) + 1) ≤
        Real.logb 2 ((2:ℝ)^(n+1) * (Real.logb (Λ:ℝ) 2 + 4)) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hu1
    have hsplit2 : Real.logb 2 ((2:ℝ)^(n+1) * (Real.logb (Λ:ℝ) 2 + 4)) =
        ((n:ℝ) + 1) + Real.logb 2 (Real.logb (Λ:ℝ) 2 + 4) := by
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      push_cast
      ring
    rw [hsplit2] at hlogm
    have hnR : (n:ℝ) = (Work.Analysis.EndVar.scaleCount 1 ρ L : ℝ) := by rw [hn]
    unfold absorbC
    rw [hD]
    linarith [hB, hlogm, hnR]

/-- `lmaxR` is the real cast of `smallL`. -/
theorem lmaxR_eq_smallL (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = (smallL l₁ l₂ k₁ k₂ : ℝ) := by
  unfold lmaxR smallL Work.Analysis.EndVar.lmax
  push_cast
  ring

theorem lossWeight_truncIndex_absorption :
    ∃ S : NNReal → ℝ, (∀ Λ : NNReal, 0 < S Λ) ∧
      ∀ (ρ A : ℝ) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ), 0 < ρ → 0 ≤ A →
        ((Nat.log2 (Work.KMTAreas.A7.truncIndex ρ Λ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) + 1) : ℝ)
            + 2) ^ 2 *
          ((1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A *
            (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂))
        ≤ S Λ * Work.KMTAreas.A7.lossWeight (A + 4) ρ l₁ l₂ k₁ k₂ := by
  refine ⟨absorbS, fun Λ => absorbS_pos Λ, ?_⟩
  intro ρ A Λ l₁ l₂ k₁ k₂ hρ hA
  set L : ℕ := smallL l₁ l₂ k₁ k₂ with hL
  have hlmax : lmaxR l₁ l₂ k₁ k₂ = (L:ℝ) := by simpa using lmaxR_eq_smallL l₁ l₂ k₁ k₂
  rw [hlmax]
  set e : ℝ := (2:ℝ) ^ (2 * ρ * (L:ℝ)) with he
  set W : ℝ := (1 + (L:ℝ)) ^ (4:ℝ) with hW
  set P : ℝ := (1 + (L:ℝ)) ^ A * (2:ℝ) ^ (A * ρ * (L:ℝ)) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  have hLnn : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  -- bound the RM cost by `(e + c)²`
  have hcrux := truncIndex_log2_add_two_le ρ hρ Λ L
  have hnc : (Nat.log2 (truncIndex ρ Λ L + 1) : ℝ) + 2 ≤ e + absorbC Λ := by
    have hsc := scaleCount_le_two_rpow ρ L
    rw [he]; linarith
  have hc1 : 1 ≤ absorbC Λ := le_trans (by norm_num) (absorbC_ge_seven Λ)
  have hW1 : 1 ≤ W := by rw [hW]; exact Real.one_le_rpow (by nlinarith) (by norm_num)
  have he1 : 1 ≤ e := by rw [he]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hsq1 : ((Nat.log2 (truncIndex ρ Λ L + 1) : ℝ) + 2)^2 ≤ (e + absorbC Λ)^2 := by
    have h0 : 0 ≤ (Nat.log2 (truncIndex ρ Λ L + 1) : ℝ) + 2 := by positivity
    exact pow_le_pow_left₀ h0 hnc 2
  have hfin : (e + absorbC Λ)^2 ≤ 4 * (absorbC Λ)^2 * W * e^2 :=
    sq_add_le_four_mul (absorbC Λ) W e hc1 hW1 he1
  have hkey : ((Nat.log2 (truncIndex ρ Λ L + 1) : ℝ) + 2)^2 ≤ 4 * (absorbC Λ)^2 * W * e^2 :=
    le_trans hsq1 hfin
  have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hPpos)
  -- unfold the loss weight and factor out the `ℓ²`-weight
  rw [lossWeight]
  rw [hlmax]
  have halg := lossAbsorb_algebra A ρ (L:ℝ) hLnn
  rw [halg]
  rw [← hW, ← he, ← hP]
  have hgoal : absorbS Λ * ((W * e^2) * P) = (4 * (absorbC Λ)^2 * W * e^2) * P := by
    unfold absorbS; ring
  rw [hgoal]
  exact hmul

end

end Work.KMTAreas.A7
