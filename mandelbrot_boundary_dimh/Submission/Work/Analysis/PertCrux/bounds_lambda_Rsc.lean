import Mathlib

namespace Work.Analysis.PertCrux

/-!
# Bounds on `Λ` and `Rsc` in terms of `Ξ'`

Auxiliary numeric estimates for the perturbation crux.  With `Ξ' ≥ 10`,
`MK, CW, Rgl ≤ Ξ'`, `Λ ≥ 64` and
`Λ ≤ 10^6 (Ξ' + MK + CW + Rgl + 1)^3 + 10^6`, Taylor-style bookkeeping
bounds `Ξ' + 3Λ + MK + 5CW + 2`, its square, and `Λ` itself by powers of `Ξ'`.

The key observation making a *two-sided* bound on
`T = Ξ' + 3Λ + MK + 5CW + 2` possible is that `Λ ≥ 64` together with the
upper bound on `Λ` forces `Ξ' + MK + CW + Rgl + 1 > -1`, hence
`MK + CW ≥ -2Ξ' - 2` and `CW ≥ -3Ξ' - 2`; this supplies the lower bound on
`T` needed to control `T^2`.
-/

/-- If `S^3 > -1` then `S > -1` (used to convert the lower bound on the cube
into a lower bound on `S`). -/
private lemma neg_one_lt_of_cube {S Λ : ℝ} (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * S ^ 3 + 10 ^ 6) : -1 < S := by
  have hS3 : (-1:ℝ) < S ^ 3 := by nlinarith [hΛ64, hΛUB]
  have hfac : S ^ 3 + 1 = (S + 1) * (S ^ 2 - S + 1) := by ring
  have hpos : 0 < S ^ 2 - S + 1 := by nlinarith [sq_nonneg (S - 1/2)]
  have hpp : 0 < (S + 1) * (S ^ 2 - S + 1) := by nlinarith [hS3, hfac]
  nlinarith [hpos, hpp]

/-- `Λ ≤ 68922000 * Ξ'^3`.  Writing `S = Ξ' + MK + CW + Rgl + 1`, we have
`S ≤ 4Ξ' + 1 ≤ (41/10)Ξ'` when `S ≥ 0`, while for `S ≤ 0` the bound
`Λ ≤ 10^6 S^3 + 10^6 ≤ 10^6 ≤ 68922000 Ξ'^3` is immediate. -/
private lemma lam_le {Ξ' MK CW Rgl Λ : ℝ} (hΞ' : 10 ≤ Ξ')
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRglΞ : Rgl ≤ Ξ')
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6) :
    Λ ≤ 68922000 * Ξ' ^ 3 := by
  have hX3 : (1000:ℝ) ≤ Ξ' ^ 3 := by
    have h : (10:ℝ) ^ 3 ≤ Ξ' ^ 3 := pow_le_pow_left₀ (by norm_num) hΞ' 3
    norm_num at h; exact h
  by_cases hS : 0 ≤ Ξ' + MK + CW + Rgl + 1
  · have hSle : Ξ' + MK + CW + Rgl + 1 ≤ 4 * Ξ' + 1 := by linarith
    have hcube : (Ξ' + MK + CW + Rgl + 1) ^ 3 ≤ (4 * Ξ' + 1) ^ 3 :=
      pow_le_pow_left₀ hS hSle 3
    have h4 : 4 * Ξ' + 1 ≤ (41/10) * Ξ' := by linarith
    have hcube2 : (4 * Ξ' + 1) ^ 3 ≤ ((41/10) * Ξ') ^ 3 :=
      pow_le_pow_left₀ (by linarith) h4 3
    have hexp : ((41/10) * Ξ') ^ 3 = (68921/1000) * Ξ' ^ 3 := by ring
    nlinarith [hΛUB, hcube, hcube2, hexp, hX3]
  · rw [not_le] at hS
    have hS3 : (Ξ' + MK + CW + Rgl + 1) ^ 3 ≤ 0 := by
      nlinarith [hS, sq_nonneg (Ξ' + MK + CW + Rgl + 1)]
    nlinarith [hΛUB, hS3, hX3]

/-- Two-sided bound `|Ξ' + 3Λ + MK + 5CW + 2| ≤ 2.11 * 10^8 * Ξ'^3`.
The upper bound uses `lam_le` and `MK, CW ≤ Ξ'`; the lower bound uses the
forced inequality `MK + CW ≥ -2Ξ' - 2` together with `Λ ≥ 64`. -/
private lemma T_abs_le {Ξ' MK CW Rgl Λ : ℝ} (hΞ' : 10 ≤ Ξ')
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRglΞ : Rgl ≤ Ξ')
    (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6) :
    |Ξ' + 3 * Λ + MK + 5 * CW + 2| ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 := by
  have hΛ : Λ ≤ 68922000 * Ξ' ^ 3 := lam_le hΞ' hMKΞ hCWΞ hRglΞ hΛUB
  have hX2 : (100:ℝ) ≤ Ξ' ^ 2 := by nlinarith [hΞ']
  have hX3 : (1000:ℝ) ≤ Ξ' ^ 3 := by nlinarith [hΞ', hX2]
  have hSgt : -1 < Ξ' + MK + CW + Rgl + 1 := neg_one_lt_of_cube hΛ64 hΛUB
  have hMKCW : -2 * Ξ' - 2 < MK + CW := by linarith
  have hCWlb : -3 * Ξ' - 2 < CW := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hMKCW, hCWlb, hΛ64, hΞ', hX2, hX3]
  · nlinarith [hMKΞ, hCWΞ, hΛ, hΞ', hX2, hX3]

theorem bounds_lambda_Rsc
    {Ξ' MK CW Rgl Λ dtau Rsc : ℝ} {m : ℕ}
    (hΞ' : 10 ≤ Ξ')
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRglΞ : Rgl ≤ Ξ')
    (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6)
    (hdtauΛ : dtau ≤ Λ / 16)
    (hRscUB : Rsc ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + MK + Λ + 4)
    (hmUB : (m : ℝ) ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + 2) :
    Ξ' + 3 * Λ + MK + 5 * CW + 2 ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 ∧
    (m : ℝ) ≤ 4.6 * 10 ^ 16 * Ξ' ^ 6 ∧
    Rsc + 1 ≤ 4.7 * 10 ^ 16 * Ξ' ^ 6 ∧
    dtau ≤ 4.4 * 10 ^ 6 * Ξ' ^ 3 := by
  have hX6 : (10:ℝ) ^ 6 ≤ Ξ' ^ 6 := pow_le_pow_left₀ (by norm_num) hΞ' 6
  have hΛ : Λ ≤ 68922000 * Ξ' ^ 3 := lam_le hΞ' hMKΞ hCWΞ hRglΞ hΛUB
  have hTabs : |Ξ' + 3 * Λ + MK + 5 * CW + 2| ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 :=
    T_abs_le hΞ' hMKΞ hCWΞ hRglΞ hΛ64 hΛUB
  have hT2 : (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 ≤ 44521000000000000 * Ξ' ^ 6 := by
    have hBnn : 0 ≤ 2.11 * 10 ^ 8 * Ξ' ^ 3 := by
      have hp : (0:ℝ) ≤ Ξ' := by linarith
      positivity
    have h1 : (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 ≤ (2.11 * 10 ^ 8 * Ξ' ^ 3) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hBnn]; exact hTabs
    have h2 : (2.11 * 10 ^ 8 * Ξ' ^ 3) ^ 2 = 44521000000000000 * Ξ' ^ 6 := by ring
    linarith [h1, h2]
  have hXle6 : Ξ' ≤ Ξ' ^ 6 := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ Ξ' by linarith) (by norm_num : 1 ≤ 6)
    simpa using h
  have hX3le6 : Ξ' ^ 3 ≤ Ξ' ^ 6 := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ Ξ' by linarith) (by norm_num : 3 ≤ 6)
    simpa using h
  have hΛ6 : Λ ≤ 68922000 * Ξ' ^ 6 := by nlinarith [hΛ, hX3le6]
  have h5 : (5:ℝ) ≤ Ξ' ^ 6 := by nlinarith [hX6]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (le_abs_self _) hTabs
  · nlinarith [hmUB, hT2, hX6]
  · nlinarith [hRscUB, hT2, hMKΞ, hXle6, hΛ6, h5]
  · nlinarith [hdtauΛ, hΛ]

end Work.Analysis.PertCrux
