import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/EpsFarCorrLe.lean`

The far-leg `ε`-correction scalar comparison
`𝓜·ε^{-1/2} ≤ 𝓜 + √(𝓜(ρ+μ)ℓ³)` of FS `lem:Roughbounds` (the `ε`-split), with
`𝓜 = bigMV v μ`, `ℓ = ell v μ`, `ε = epsFar v μ ρ = √(𝓜/((ρ+μ)ℓ³))`.

The whole content is elementary real analysis, and it is proved here *self-containedly*
(the file does not import `RpowThreeQuartersLe`/`MulRpowNegQuarterLe`, whose proofs live
elsewhere, so no `sorryAx` can enter through this module):

* `rpowThreeQuartersAux` — `u^{3/4} ≤ u + u^{1/2}` for `u ≥ 0`.  Case split: if `u ≥ 1`
  then `u^{3/4} ≤ u^1 = u`; if `u ≤ 1` then `u^{3/4} ≤ u^{1/2}`.
* `mulRpowNegQuarterAux` — `u·u^{−1/4} = u^{3/4}` for `u ≥ 0`.
* `mulRpowNegQuarterAux2` — the general form `M·(M/Y)^{−1/4} ≤ M + √(M·Y)` for
  `M, Y ≥ 0`: with `u = M/Y` (and `Y > 0`), `M = Y·u`, so the left side is
  `Y·u^{3/4}` and the right side is `Y·(u + u^{1/2})`.

The target `EpsFarCorrLe` is then the instance `M = bigMV v μ`, `Y = (ρ+μ)ℓ³`, after
rewriting `ε^{−1/2} = (M/Y)^{−1/4}` (`Real.sqrt_eq_rpow` + `Real.rpow_mul`).
-/

namespace Work.BoseFixR

/-! ## Auxiliary scalar inequalities -/

/-- `u · u^{-1/4} = u^{3/4}` for `u ≥ 0`. -/
lemma mulRpowNegQuarterAux (u : ℝ) (hu : 0 ≤ u) : u * u ^ (-(1 / 4 : ℝ)) = u ^ (3 / 4 : ℝ) := by
  rcases eq_or_lt_of_le hu with h0 | h0
  · subst h0
    rw [Real.zero_rpow (by norm_num : (-(1 / 4 : ℝ)) ≠ 0), mul_zero,
        Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0)]
  · have h : u ^ (1 + -(1 / 4 : ℝ)) = u ^ (1 : ℝ) * u ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_add h0 1 (-(1 / 4))
    rw [show (1 : ℝ) + -(1 / 4) = 3 / 4 by norm_num, Real.rpow_one] at h
    exact h.symm

/-- The elementary real inequality behind the `ε`-correction: `u^{3/4} ≤ u + u^{1/2}` for
`u ≥ 0`.  For `u ≥ 1` we have `u^{3/4} ≤ u^1 = u`; for `u ≤ 1` we have `u^{3/4} ≤ u^{1/2}`
(and `u^{1/2} ≥ 0`, `u ≥ 0`). -/
lemma rpowThreeQuartersAux (u : ℝ) (hu : 0 ≤ u) : u ^ (3 / 4 : ℝ) ≤ u + u ^ (1 / 2 : ℝ) := by
  rcases lt_or_ge u 1 with h1 | h1
  · rcases eq_or_lt_of_le hu with h0 | h0
    · subst h0; norm_num
    · have h23 : u ^ (3 / 4 : ℝ) ≤ u ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge h0 (le_of_lt h1) (by norm_num)
      have h3 : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu _
      linarith
  · have h23 : u ^ (3 / 4 : ℝ) ≤ u ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    rw [Real.rpow_one] at h23
    have h3 : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu _
    linarith

/-- `M·(M/Y)^{−1/4} ≤ M + √(M·Y)` for `M, Y ≥ 0`.  This is the `u`-substitution form of
`u^{3/4} ≤ u + u^{1/2}` (`u = M/Y`), i.e. `M^{3/4}Y^{1/4} ≤ M + √(MY)`. -/
lemma mulRpowNegQuarterAux2 (M Y : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) :
    M * (M / Y) ^ (-(1 / 4 : ℝ)) ≤ M + Real.sqrt (M * Y) := by
  rcases lt_or_ge 0 Y with hYpos | hYle
  · set u := M / Y with hu
    have hu0 : 0 ≤ u := div_nonneg hM hYpos.le
    have hMeq : M = Y * u := by
      rw [hu, mul_comm Y (M / Y)]
      exact (div_mul_cancel₀ M (ne_of_gt hYpos)).symm
    have hL : M * u ^ (-(1 / 4 : ℝ)) = Y * u ^ (3 / 4 : ℝ) := by
      rw [hMeq, mul_assoc, mulRpowNegQuarterAux u hu0]
    have hR : M + Real.sqrt (M * Y) = Y * (u + u ^ (1 / 2 : ℝ)) := by
      rw [hMeq]
      have hs : Real.sqrt (Y * u * Y) = Y * u ^ (1 / 2 : ℝ) := by
        rw [show Y * u * Y = (Y * Y) * u by ring, Real.sqrt_mul (mul_self_nonneg Y),
            Real.sqrt_mul_self hYpos.le, Real.sqrt_eq_rpow]
      rw [hs]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left (rpowThreeQuartersAux u hu0) hYpos.le
  · have hY0 : Y = 0 := le_antisymm hYle hY
    subst hY0
    rw [div_zero, Real.zero_rpow (by norm_num : (-(1 / 4 : ℝ)) ≠ 0), mul_zero,
        Real.sqrt_zero, add_zero]
    exact hM

/-! ## The target -/

/-- The crux step of the far-leg `ε`-correction: `𝓜·ε^{-1/2} ≤ 𝓜 + √(𝓜(ρ+μ)ℓ³)`, where
`𝓜 = bigMV v μ = Work.BoseBox.bigM (paramsAt μ (a v)) (a v) μ`, `ℓ = ell v μ = sideAt μ (a v)`
and `ε = epsFar v μ ρ = Real.sqrt (𝓜/((ρ+μ)ℓ³))`.

Computation: writing `x = 𝓜/((ρ+μ)ℓ³) > 0`, `Real.sqrt x = x^(1/2)` and
`ε^(−1/2) = x^(−1/4)`, so `𝓜·ε^{−1/2} = 𝓜^{3/4}((ρ+μ)ℓ³)^{1/4}`; the substitution
`u = x` gives `𝓜^{3/4}((ρ+μ)ℓ³)^{1/4} = (ρ+μ)ℓ³·u^{3/4}` and
`𝓜 + √(𝓜(ρ+μ)ℓ³) = (ρ+μ)ℓ³·(u + u^{1/2})`, so it is `u^{3/4} ≤ u + u^{1/2}`
(`Work.BoseFixR.RpowThreeQuartersLe`, also being proved separately).
(`𝓜 > 0` follows from `Work.BoseBox.bigM_pos_of_params hμ hav` via
`Work.BoseFixR.bigMV_nonneg`'s route.) -/
theorem EpsFarCorrLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ)
    (hℓ : 0 < Work.BoseFixR.ell v μ) :
    Work.BoseFixR.bigMV v μ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))
      ≤ Work.BoseFixR.bigMV v μ
        + Real.sqrt (Work.BoseFixR.bigMV v μ * (ρ + μ) * Work.BoseFixR.ell v μ ^ 3) := by
  have hM : 0 ≤ bigMV v μ := bigMV_nonneg hμ hav
  have hY : 0 ≤ (ρ + μ) * ell v μ ^ 3 := mul_nonneg (by linarith) (pow_nonneg hℓ.le 3)
  have hx : 0 ≤ bigMV v μ / ((ρ + μ) * ell v μ ^ 3) := div_nonneg hM hY
  have hε : (bigMV v μ / ((ρ + μ) * ell v μ ^ 3)) ^ (-(1 / 4 : ℝ))
      = (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
    rw [epsFar, Real.sqrt_eq_rpow]
    have hmul : (bigMV v μ / ((ρ + μ) * ell v μ ^ 3)) ^ ((1 / 2 : ℝ) * (-(1 / 2 : ℝ)))
        = ((bigMV v μ / ((ρ + μ) * ell v μ ^ 3)) ^ (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_mul hx (1 / 2) (-(1 / 2))
    rw [show (1 : ℝ) / 2 * (-(1 / 2)) = -(1 / 4) by norm_num] at hmul
    exact hmul
  have hmain := mulRpowNegQuarterAux2 (bigMV v μ) ((ρ + μ) * ell v μ ^ 3) hM hY
  rw [show bigMV v μ * ((ρ + μ) * ell v μ ^ 3) = bigMV v μ * (ρ + μ) * ell v μ ^ 3 by ring]
    at hmain
  rw [← hε]
  exact hmain

end Work.BoseFixR
