/-
# The exceptional scales are bounded in terms of `C₀` alone

This module proves `Work.KMTAreas.A7.ExceptionalSupport`, the structural fact behind the
crude bound on the exceptional part of the KMT large-scale estimate: if a scale `N` is
*admissible* (`l₁,l₂,k₁,k₂ ≤ l_{(N)} = C₀ LogLog N`), *large* (`N > 2^{2^u}`, `u = ⌊2^{2ρL}⌋`,
`L = max(max l₁ l₂)(max k₁ k₂)`) and *not* in the main regime (`k + 2u ≤ Log N`), then `N` and all
four parameters are bounded in terms of `C₀` alone, uniformly in `ρ ∈ (0,1]`.

## The mathematics

Write `R = Log N = ⌊log₂ N⌋`, `M = max k₁ k₂` and `u = scaleCount 1 ρ M = ⌊2^{2ρM}⌋`.  Since
`M ≤ L`, the large-scale hypothesis `2^{2^u} ≤ N` gives

  `2^{u} ≤ Log N = R`     and hence     `u ≤ log₂ R`.

Being outside the main regime gives `k + 2u > R` for one of `k = k₁, k₂`, so, using
`k ≤ l_{(N)} = C₀ · log₂(R+2)`,

  `R + 1 ≤ C₀ · log₂ (R+2) + 2 · log₂ R`.                                        (★)

The right-hand side is of size `O(C₀ log R)`, so (★) forces `R` to be `O(C₀ log C₀)`; here we
only need the generous bound `R + 1 ≤ 8(C₀+2)² + 64` (and the companion bound on `C₀ log₂(R+2)`),
which is the content of the pure-arithmetic lemma `Work.KMTAreas.A7.ExcNumericBound` (proved in
`ExcNumericBound.lean`, by a colleague, independently of this file).  Granting it, the parameter
bound follows from `lᵢ ≤ l_{(N)} = C₀ log₂ (R+2)` and `N ≤ 2^{R+1}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ExcDefs
import Submission.Work.KMTAreas.A7.ExcNumericBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

namespace ExcSupport

/-- The scale count `u = ⌊C₂ 2^{2ρl}⌋` is monotone in the height `l`, for `ρ ≥ 0`. -/
lemma scaleCount_mono (C₂ : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : Monotone (scaleCount C₂ ρ) := by
  intro l l' hl
  simp only [scaleCount, Int.floor_toNat]
  apply Nat.floor_mono
  have hlR : (l : ℝ) ≤ (l' : ℝ) := by exact_mod_cast hl
  have hexp : 2 * ρ * (l : ℝ) ≤ 2 * ρ * (l' : ℝ) := by nlinarith
  have hpow : (2 : ℝ) ^ (2 * ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (l' : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

end ExcSupport

theorem ExceptionalSupport (C₀ : ℕ) (ρ : ℝ) (l₁ l₂ k₁ k₂ N : ℕ) (hC₀ : 1 ≤ C₀)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hl₁ : l₁ ≤ Work.Analysis.EndVar.heightScale C₀ N)
    (hl₂ : l₂ ≤ Work.Analysis.EndVar.heightScale C₀ N)
    (hk₁ : k₁ ≤ Work.Analysis.EndVar.heightScale C₀ N)
    (hk₂ : k₂ ≤ Work.Analysis.EndVar.heightScale C₀ N)
    (hmain : ¬ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N)
    (hsplit : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N) :
    N ≤ 2 ^ Work.KMTAreas.A7.excBnd C₀ ∧ l₁ ≤ Work.KMTAreas.A7.excBnd C₀ ∧
      l₂ ≤ Work.KMTAreas.A7.excBnd C₀ ∧ k₁ ≤ Work.KMTAreas.A7.excBnd C₀ ∧
      k₂ ≤ Work.KMTAreas.A7.excBnd C₀ := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hρ1' : ρ ≤ 1 := hρ1
  set R := Nat.log 2 (max N 2) with hR
  have hR1 : 1 ≤ R := by
    rw [hR]
    refine Nat.le_log_of_pow_le (by norm_num : 1 < 2) ?_
    exact le_max_right N 2
  set M := max k₁ k₂ with hM
  set L := max (max l₁ l₂) (max k₁ k₂) with hL
  have hML : M ≤ L := by rw [hM, hL]; exact le_max_right _ _
  -- the scale count at `M` is at most the scale count at `L`
  have huM : scaleCount 1 ρ M ≤ scaleCount 1 ρ L := ExcSupport.scaleCount_mono 1 hρ0 hML
  have hsplit' : 2 ^ (2 ^ scaleCount 1 ρ L) < N := hsplit
  have h2u : 2 ^ (2 ^ scaleCount 1 ρ M) ≤ N := by
    have h1 : (2 : ℕ) ^ scaleCount 1 ρ M ≤ 2 ^ scaleCount 1 ρ L :=
      Nat.pow_le_pow_right (by norm_num) huM
    exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) (le_of_lt hsplit')
  -- `2 ^ u ≤ R`
  have h2u_le_R : 2 ^ scaleCount 1 ρ M ≤ R := by
    have h1 : 2 ^ scaleCount 1 ρ M ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) h2u
    rw [hR]
    exact h1.trans (Nat.log_mono_right (le_max_left N 2))
  have hu_le_R : scaleCount 1 ρ M ≤ Nat.log 2 R := Nat.le_log_of_pow_le (by norm_num) h2u_le_R
  -- the main regime is false in terms of `R` and `M`
  have hlogN : (logN N).toNat = R := by simp only [logN, hR, Int.toNat_natCast]
  have hmain' : ¬ (k₁ + 2 * scaleCount 1 ρ M ≤ R ∧ k₂ + 2 * scaleCount 1 ρ M ≤ R) := by
    intro hc
    exact hmain (by rw [mainRegime, hlogN, ← hM]; exact hc)
  have hcase : R < k₁ + 2 * scaleCount 1 ρ M ∨ R < k₂ + 2 * scaleCount 1 ρ M := by
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    exact hmain' ⟨hcon.1, hcon.2⟩
  -- the height bound in terms of `R`
  have hheight : ∀ k : ℕ, k ≤ Work.Analysis.EndVar.heightScale C₀ N → k ≤ C₀ * Nat.log 2 (R + 2) := by
    intro k hk
    have hh : Work.Analysis.EndVar.heightScale C₀ N = C₀ * Nat.log 2 (R + 2) := by
      simp only [Work.Analysis.EndVar.heightScale, Work.Analysis.EndVar.logLogN, hR]
    rwa [hh] at hk
  -- the key inequality (★)
  have hkey : R + 1 ≤ C₀ * Nat.log 2 (R + 2) + 2 * Nat.log 2 R := by
    have key : ∀ k : ℕ, k ≤ C₀ * Nat.log 2 (R + 2) → R < k + 2 * scaleCount 1 ρ M →
        R + 1 ≤ C₀ * Nat.log 2 (R + 2) + 2 * Nat.log 2 R := by
      intro k hk hkR
      have hu : 2 * scaleCount 1 ρ M ≤ 2 * Nat.log 2 R := Nat.mul_le_mul_left 2 hu_le_R
      omega
    rcases hcase with hc | hc
    · exact key k₁ (hheight k₁ hk₁) hc
    · exact key k₂ (hheight k₂ hk₂) hc
  obtain ⟨hbound, hclog⟩ := ExcNumericBound C₀ R hC₀ hR1 hkey
  have hexc : R + 1 ≤ excBnd C₀ := by simpa [excBnd] using hbound
  have hclog' : C₀ * Nat.log 2 (R + 2) ≤ excBnd C₀ := by simpa [excBnd] using hclog
  have hparam : ∀ k : ℕ, k ≤ Work.Analysis.EndVar.heightScale C₀ N → k ≤ excBnd C₀ :=
    fun k hk => (hheight k hk).trans hclog'
  have hN : N ≤ 2 ^ excBnd C₀ := by
    have h1 : N < 2 ^ (R + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
      rw [← hR] at h
      exact lt_of_le_of_lt (le_max_left N 2) h
    exact le_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hexc))
  exact ⟨hN, hparam l₁ hl₁, hparam l₂ hl₂, hparam k₁ hk₁, hparam k₂ hk₂⟩

end Work.KMTAreas.A7
