import Mathlib
import Submission.Work.Analysis.PertCrux.lam_bound
import Submission.Work.Analysis.PertCrux.T_sq_bound

/-!
# PertCrux · `crux_bounds`

Numeric bookkeeping for the perturbation layer of the Shishikura argument.  From `Ξ' ≥ 10`,
`MK, CW, RG ≤ Ξ'`, `Λ ≥ 64`, `Λ ≤ 10^6 (Ξ' + MK + CW + RG + 1)^3 + 10^6`, `dtau ≤ Λ/16`,
`Rsc ≤ 200 Λ^2` and `m ≤ (Ξ' + 3Λ + MK + 5CW + 2)^2 + 2`, conclude the four explicit bounds

* `Λ ≤ 68922000 Ξ'^3`      — the delegated `Work.Analysis.PertCrux.lam_bound` (the cube
  hypothesis saturated at `Ξ' + MK + CW + RG + 1 ≤ 4Ξ' + 1 ≤ 4.1Ξ'`, with `10^6 ≤ 1000 Ξ'^3`),
* `dtau ≤ 4400000 Ξ'^3`    — from `Λ/16` and the bound on `Λ` (`68922000/16 = 4307625`),
* `Rsc ≤ 9.6·10^17 Ξ'^6`   — from `200 Λ^2` and the bound on `Λ` (`200·68922000² ≤ 9.6·10^17`),
* `m ≤ 4.6·10^16 Ξ'^6`     — the delegated `Work.Analysis.PertCrux.T_sq_bound`, the two-sided
  bound `(Ξ' + 3Λ + MK + 5CW + 2)^2 ≤ (2.11·10^8)^2 Ξ'^6 = 4.4521·10^16 Ξ'^6`, which needs
  `Λ ≥ 64` to manufacture a *lower* bound on `Ξ' + 3Λ + MK + 5CW + 2` (the monotone hypotheses
  only bound `MK, CW` above).

This file is the assembly: the two hard numeric inputs `lam_bound` and `T_sq_bound` are proved
separately, and here only the three linear/monotone chases are performed.
-/

namespace Work.Analysis.PertCrux

theorem crux_bounds {Ξ' MK CW RG Λ dtau Rsc : ℝ} {m : ℕ}
    (hΞ' : 10 ≤ Ξ') (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRGΞ : RG ≤ Ξ')
    (hΛ64 : 64 ≤ Λ)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6)
    (hdtauΛ : dtau ≤ Λ / 16)
    (hRscUB : Rsc ≤ 200 * Λ ^ 2)
    (hmUB : (m : ℝ) ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + 2) :
    Λ ≤ 68922000 * Ξ' ^ 3 ∧ dtau ≤ 4400000 * Ξ' ^ 3 ∧
      Rsc ≤ 960000000000000000 * Ξ' ^ 6 ∧ (m : ℝ) ≤ 46000000000000000 * Ξ' ^ 6 := by
  -- the two delegated numeric inputs
  have hΛ : Λ ≤ 68922000 * Ξ' ^ 3 := lam_bound hΞ' hMKΞ hCWΞ hRGΞ hΛUB
  have hT2 : (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 ≤ 44521000000000000 * Ξ' ^ 6 :=
    T_sq_bound hΞ' hMKΞ hCWΞ hRGΞ hΛ64 hΛUB
  have hΛnn : (0 : ℝ) ≤ Λ := by linarith
  have hX3 : (1000 : ℝ) ≤ Ξ' ^ 3 := by
    have h : (10 : ℝ) ^ 3 ≤ Ξ' ^ 3 := pow_le_pow_left₀ (by norm_num) hΞ' 3
    norm_num at h; exact h
  have hX6 : (10 : ℝ) ^ 6 ≤ Ξ' ^ 6 := pow_le_pow_left₀ (by norm_num) hΞ' 6
  have hX6pos : (0 : ℝ) < Ξ' ^ 6 := by linarith
  have hΛ2 : Λ ^ 2 ≤ 4750242084000000 * Ξ' ^ 6 := by
    have h := pow_le_pow_left₀ hΛnn hΛ 2
    have h2 : (68922000 * Ξ' ^ 3) ^ 2 = 4750242084000000 * Ξ' ^ 6 := by ring
    linarith [h, h2]
  refine ⟨hΛ, ?_, ?_, ?_⟩
  · nlinarith [hdtauΛ, hΛ, hX3]
  · nlinarith [hRscUB, hΛ2, hX6pos]
  · nlinarith [hmUB, hT2, hX6]

end Work.Analysis.PertCrux
