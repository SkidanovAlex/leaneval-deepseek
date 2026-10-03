import Mathlib

/-!
# PertCrux · `T_sq_bound`

The squared two-sided estimate for `T = Ξ' + 3Λ + MK + 5CW + 2` used by the
perturbation layer of the Shishikura argument.

The hypotheses only bound `MK`, `CW`, `RG` *above* by `Ξ'`; nevertheless
`Λ ≥ 64` together with the cubic upper bound on `Λ` forces
`S = Ξ' + MK + CW + RG + 1 > -1`, which in turn supplies the lower bound on
`T` needed to control `T^2`.  Concretely `|T| ≤ 2.11·10^8 Ξ'^3`, and
`(2.11·10^8)^2 = 44521000000000000`.
-/

namespace Work.Analysis.PertCrux

/-- If `S³ > -1` then `S > -1`; used to turn the lower bound on the cube into a
lower bound on `S`.  Here `S³ + 1 = (S + 1)·(S² - S + 1)` and `S² - S + 1 > 0`. -/
private lemma TSB_neg_one_lt_of_cube {S Λ : ℝ} (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * S ^ 3 + 10 ^ 6) : -1 < S := by
  have hS3 : (-1 : ℝ) < S ^ 3 := by nlinarith [hΛ64, hΛUB]
  have hfac : S ^ 3 + 1 = (S + 1) * (S ^ 2 - S + 1) := by ring
  have hpos : 0 < S ^ 2 - S + 1 := by nlinarith [sq_nonneg (S - 1 / 2)]
  have hpp : 0 < (S + 1) * (S ^ 2 - S + 1) := by nlinarith [hS3, hfac]
  nlinarith [hpos, hpp]

/-- `Λ ≤ 68922000 Ξ'^3`.  Writing `S = Ξ' + MK + CW + RG + 1` we have
`S ≤ 4Ξ' + 1 ≤ (41/10)Ξ'` when `S ≥ 0`, while for `S ≤ 0` the bound
`Λ ≤ 10^6 S^3 + 10^6 ≤ 10^6 ≤ 68922000 Ξ'^3` is immediate. -/
private lemma TSB_lam_le {Ξ' MK CW RG Λ : ℝ} (hΞ' : 10 ≤ Ξ')
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRGΞ : RG ≤ Ξ')
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6) :
    Λ ≤ 68922000 * Ξ' ^ 3 := by
  have hX3 : (1000 : ℝ) ≤ Ξ' ^ 3 := by
    have h : (10 : ℝ) ^ 3 ≤ Ξ' ^ 3 := pow_le_pow_left₀ (by norm_num) hΞ' 3
    norm_num at h; exact h
  by_cases hS : 0 ≤ Ξ' + MK + CW + RG + 1
  · have hSle : Ξ' + MK + CW + RG + 1 ≤ 4 * Ξ' + 1 := by linarith
    have hcube : (Ξ' + MK + CW + RG + 1) ^ 3 ≤ (4 * Ξ' + 1) ^ 3 :=
      pow_le_pow_left₀ hS hSle 3
    have h4 : 4 * Ξ' + 1 ≤ (41 / 10) * Ξ' := by linarith
    have hcube2 : (4 * Ξ' + 1) ^ 3 ≤ ((41 / 10) * Ξ') ^ 3 :=
      pow_le_pow_left₀ (by linarith) h4 3
    have hexp : ((41 / 10) * Ξ') ^ 3 = (68921 / 1000) * Ξ' ^ 3 := by ring
    nlinarith [hΛUB, hcube, hcube2, hexp, hX3]
  · rw [not_le] at hS
    have hS3 : (Ξ' + MK + CW + RG + 1) ^ 3 ≤ 0 := by
      nlinarith [hS, sq_nonneg (Ξ' + MK + CW + RG + 1)]
    nlinarith [hΛUB, hS3, hX3]

/-- Two-sided bound `|Ξ' + 3Λ + MK + 5CW + 2| ≤ 2.11·10^8 Ξ'^3`.
The upper bound uses `TSB_lam_le` and `MK, CW ≤ Ξ'`; the lower bound uses the forced
`S > -1`, hence `MK + CW > -2Ξ' - 2` and `CW > -3Ξ' - 2`, with `Λ ≥ 64 ≥ 0`. -/
private lemma TSB_T_abs_le {Ξ' MK CW RG Λ : ℝ} (hΞ' : 10 ≤ Ξ')
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRGΞ : RG ≤ Ξ')
    (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6) :
    |Ξ' + 3 * Λ + MK + 5 * CW + 2| ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 := by
  have hΛ : Λ ≤ 68922000 * Ξ' ^ 3 := TSB_lam_le hΞ' hMKΞ hCWΞ hRGΞ hΛUB
  have hX2 : (100 : ℝ) ≤ Ξ' ^ 2 := by nlinarith [hΞ']
  have hX3 : (1000 : ℝ) ≤ Ξ' ^ 3 := by nlinarith [hΞ', hX2]
  have hSgt : -1 < Ξ' + MK + CW + RG + 1 := TSB_neg_one_lt_of_cube hΛ64 hΛUB
  have hMKCW : -2 * Ξ' - 2 < MK + CW := by linarith
  have hCWlb : -3 * Ξ' - 2 < CW := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hMKCW, hCWlb, hΛ64, hΞ', hX2, hX3]
  · nlinarith [hMKΞ, hCWΞ, hΛ, hΞ', hX2, hX3]

theorem T_sq_bound {Ξ' MK CW RG Λ : ℝ}
    (hΞ' : 10 ≤ Ξ') (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRGΞ : RG ≤ Ξ')
    (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6) :
    (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 ≤ 44521000000000000 * Ξ' ^ 6 := by
  have hTabs : |Ξ' + 3 * Λ + MK + 5 * CW + 2| ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 :=
    TSB_T_abs_le hΞ' hMKΞ hCWΞ hRGΞ hΛ64 hΛUB
  have hBnn : (0 : ℝ) ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 := by
    have hp : (0 : ℝ) ≤ Ξ' := by linarith
    positivity
  have h1 : (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 ≤ (2.11 * 10 ^ 8 * Ξ' ^ 3) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hBnn]; exact hTabs
  have h2 : (2.11 * 10 ^ 8 * Ξ' ^ 3) ^ 2 = 44521000000000000 * Ξ' ^ 6 := by ring
  linarith [h1, h2]

end Work.Analysis.PertCrux
