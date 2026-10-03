/-
# The exceptional small scales are bounded in terms of `C₀` alone

This module proves `Work.KMTAreas.A7.SmallExcSupport`, the structural fact behind the crude bound
on the *small-scale* exceptional part (`Work.KMTAreas.A7.smallExcPart`) of the KMT estimate: if a
scale `N` is

* *admissible*: `l₁,l₂,k₁,k₂ ≤ l_{(N)} = C₀ LogLog N`,
* *outside the main regime*: `¬ mainRegime ρ k₁ k₂ N`, i.e. `Log N < k + 2u` for `k = k₁` or `k₂`,
  where `u = scaleCount 1 ρ (max k₁ k₂) = ⌊2^{2ρ·max k₁ k₂}⌋`,

and `ρ ≤ 1/(8C₀)`, `C₀ ≥ 1`, then `N` and all four parameters are bounded in terms of `C₀`
alone (uniformly in `ρ`).  Consequently only finitely many lacunary scales are exceptional.

## The mathematics

Write `R = Log N = ⌊log₂ N⌋`, `M = max k₁ k₂`, `L = max (max l₁ l₂) (max k₁ k₂)` and
`L_R = Nat.log 2 (R+2)`, so that admissibility gives

  `M ≤ L ≤ l_{(N)} = C₀ · L_R`.

The hypotheses on `ρ` and `M` give `2ρM ≤ 2ρC₀ L_R ≤ L_R/4`, hence

  `u = ⌊2^{2ρM}⌋ ≤ 2^{2ρM} ≤ 2^{(1/4) log₂ (R+2)} = (R+2)^{1/4}`,

and being outside the main regime gives `R + 1 ≤ k + 2u` for `k = k₁` or `k₂`, so altogether

  `R + 1 ≤ C₀ log₂ (R+2) + 2 (R+2)^{1/4}`,

which (lemma `smallExcNumeric`) forces `R + 1 ≤ (4C₀+3)^4`.  Since `L ≤ C₀ L_R ≤ C₀ (R+1)` and
`N < 2^{R+1}`, the bound `B = C₀ (4C₀+3)^4` works for both the parameters and the scale.

## Note

The restriction `ρ ≤ 1/(8C₀)` is essential: without it the exceptional regime is unbounded (take
`C₀ = 1`, `ρ = 1`, `lᵢ = kᵢ = ⌊log₂log₂ N⌋`, `N = 2^m` for arbitrarily large `m`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Work.KMTAreas.A7.smallExcNumeric
import Submission.Work.KMTAreas.A7.scaleCount_le_rpow

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

/-- The logarithm of a natural number is at most the real logarithm base `2` of its image:
`Nat.log 2 n ≤ Real.logb 2 n`. -/
lemma natLog_cast_le_logb (n : ℕ) : (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
      have := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
      exact_mod_cast this
    have h2 := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at h2

/-- **The support of the exceptional small scales is bounded in terms of `C₀`.**  For
`ρ ≤ 1/(8C₀)`, every admissible scale outside the main regime has all its parameters and the scale
itself bounded by a constant depending only on `C₀`. -/
theorem SmallExcSupport (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ₀ : ρ ≤ 1 / (8 * (C₀ : ℝ))) :
    ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
      ¬ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N →
      max (max l₁ l₂) (max k₁ k₂) ≤ B ∧ N ≤ 2 ^ B := by
  refine ⟨C₀ * (4 * C₀ + 3) ^ 4, ?_⟩
  intro l₁ l₂ k₁ k₂ N hI hnot
  set R := Nat.log 2 (max N 2) with hR
  have hlogN : (logN N).toNat = R := by
    simp only [logN, hR, Int.toNat_natCast]
  have hperiod := hI
  simp only [inIndexSet] at hperiod
  obtain ⟨hlmax, hk₁, hk₂⟩ := hperiod
  have hhs : heightScale C₀ N = C₀ * Nat.log 2 (R + 2) := by
    simp only [heightScale, logLogN, ← hR]
  have hl : max l₁ l₂ ≤ heightScale C₀ N := by
    have h := hlmax
    rw [← Nat.cast_max] at h
    exact_mod_cast h
  have hk₁n : k₁ ≤ heightScale C₀ N := by exact_mod_cast hk₁
  have hk₂n : k₂ ≤ heightScale C₀ N := by exact_mod_cast hk₂
  have hL : max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ N := max_le hl (max_le hk₁n hk₂n)
  have hk₁' : k₁ ≤ C₀ * Nat.log 2 (R + 2) := by rw [← hhs]; exact hk₁n
  have hk₂' : k₂ ≤ C₀ * Nat.log 2 (R + 2) := by rw [← hhs]; exact hk₂n
  have hM : max k₁ k₂ ≤ C₀ * Nat.log 2 (R + 2) := max_le hk₁' hk₂'
  -- the bound on the auxiliary scale `u = ⌊2^{2ρ max k₁ k₂}⌋`
  have huR : (uScale ρ (max k₁ k₂) : ℝ) ≤ ((R : ℝ) + 2) ^ ((1:ℝ)/4) := by
    have := scaleCount_le_rpow ρ C₀ (max k₁ k₂) R hC₀ hρ hρ₀ hM
    simpa [uScale] using this
  -- being outside the main regime
  have hmain' : ¬ (k₁ + 2 * uScale ρ (max k₁ k₂) ≤ R ∧ k₂ + 2 * uScale ρ (max k₁ k₂) ≤ R) := by
    intro hc
    exact hnot (by rw [mainRegime, hlogN]; exact hc)
  have hcase : R < k₁ + 2 * uScale ρ (max k₁ k₂) ∨ R < k₂ + 2 * uScale ρ (max k₁ k₂) := by
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    exact hmain' ⟨hcon.1, hcon.2⟩
  -- the real inequality of the numeric lemma
  have hkey : ∀ k : ℕ, k ≤ C₀ * Nat.log 2 (R + 2) → R < k + 2 * uScale ρ (max k₁ k₂) →
      (R : ℝ) + 1 ≤ (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2) + 2 * ((R : ℝ) + 2) ^ ((1:ℝ)/4) := by
    intro k hk hkR
    have h1 : R + 1 ≤ k + 2 * uScale ρ (max k₁ k₂) := by omega
    have h2 : ((k + 2 * uScale ρ (max k₁ k₂) : ℕ) : ℝ)
        = (k : ℝ) + 2 * (uScale ρ (max k₁ k₂) : ℝ) := by push_cast; ring
    have h3 : ((R : ℝ) + 1) ≤ (k:ℝ) + 2 * (uScale ρ (max k₁ k₂) : ℝ) := by
      have h4 : ((R+1 : ℕ) : ℝ) ≤ ((k + 2 * uScale ρ (max k₁ k₂) : ℕ) : ℝ) := by
        exact_mod_cast h1
      rw [h2] at h4
      push_cast at h4
      linarith
    have h5 : (k : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2) := by
      have hk' : (k : ℝ) ≤ (C₀ : ℝ) * (Nat.log 2 (R + 2) : ℝ) := by exact_mod_cast hk
      have hL' : (Nat.log 2 (R + 2) : ℝ) ≤ Real.logb 2 ((R : ℝ) + 2) := by
        have := natLog_cast_le_logb (R + 2)
        simpa using this
      exact le_trans hk' (mul_le_mul_of_nonneg_left hL' (by positivity))
    have h6 : 2 * (uScale ρ (max k₁ k₂) : ℝ) ≤ 2 * ((R:ℝ)+2)^((1:ℝ)/4) := by linarith [huR]
    linarith
  have hreal : (R : ℝ) + 1 ≤
      (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2) + 2 * ((R : ℝ) + 2) ^ ((1:ℝ)/4) := by
    rcases hcase with hc | hc
    · exact hkey k₁ hk₁' hc
    · exact hkey k₂ hk₂' hc
  have hnum : R + 1 ≤ (4 * C₀ + 3) ^ 4 := smallExcNumeric C₀ R hC₀ hreal
  -- `Nat.log 2 (R+2) ≤ R+1`
  have hLR : Nat.log 2 (R + 2) ≤ R + 1 := by
    have h1 : R + 2 ≤ 2 ^ (R + 1) := by
      have := Nat.lt_two_pow_self (n := R + 1)
      omega
    calc Nat.log 2 (R + 2) ≤ Nat.log 2 (2 ^ (R + 1)) := Nat.log_mono_right h1
      _ = R + 1 := Nat.log_pow (by norm_num) (R + 1)
  have hLbound : max (max l₁ l₂) (max k₁ k₂) ≤ C₀ * (4 * C₀ + 3) ^ 4 := by
    calc max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ N := hL
      _ = C₀ * Nat.log 2 (R + 2) := hhs
      _ ≤ C₀ * (R + 1) := Nat.mul_le_mul_left C₀ hLR
      _ ≤ C₀ * (4 * C₀ + 3) ^ 4 := Nat.mul_le_mul_left C₀ hnum
  have hNbound : N ≤ 2 ^ (C₀ * (4 * C₀ + 3) ^ 4) := by
    have h1 : N < 2 ^ (R + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
      rw [← hR] at h
      exact lt_of_le_of_lt (le_max_left N 2) h
    have h2 : R + 1 ≤ C₀ * (4 * C₀ + 3) ^ 4 := by
      calc R + 1 ≤ (4 * C₀ + 3) ^ 4 := hnum
        _ ≤ C₀ * (4 * C₀ + 3) ^ 4 := Nat.le_mul_of_pos_left _ (by omega : 0 < C₀)
    exact le_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2))
  exact ⟨hLbound, hNbound⟩

end

end Work.KMTAreas.A7
