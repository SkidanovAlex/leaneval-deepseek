import ChallengeDeps
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Arith.bigM_ge_eight`

The matrix-localisation window of FS `eq:DefM`,

    𝓜 = bigM (paramsAt μ a) a μ = K_M(μa³)^{-1/4} = (μa³)^{-1/323-1/4},

is `≥ 8` for all admissible chemical potentials, provided the diluteness cap
`ε₀` is chosen small enough.  This is the hypothesis under which the §6 window
arithmetic (`gradeMw_spec`: `3 ≤ Mw`, `𝓜/4 ≤ Mw ≤ 𝓜/2`) applies.

The choice `ε₀ = 8^{-1292/327}` is exactly the threshold where
`(μa³)^{-1/323-1/4} = 8`, since `(1/323 + 1/4)·(1292/327) = 1`.
-/

namespace Work.BoseFixB2.Arith

open _root_.BoseGases

/-- `bigM (paramsAt μ a) a μ` is the FS window `(μa³)^{-1/323-1/4}`
(the product of `K_M = (μa³)^{-1/323}` and `(μa³)^{-1/4}`). -/
lemma bigM_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3) :
    Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) (_root_.BoseGases.a v) μ
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(327 / 1292) : ℝ) := by
  rw [Work.BoseBox.bigM]
  have hK : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KM
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((-1) / 323 : ℝ) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [hK, ← Real.rpow_add ht0]
  congr 1
  norm_num

/-- The window inequality: below the diluteness cap `ε₀ = 8^{-1292/327}` the
window is at least `8`. -/
lemma eight_le_rpow_neg {t : ℝ} (ht0 : 0 < t) (htle : t ≤ (8 : ℝ) ^ (-(1292 / 327) : ℝ)) :
    (8 : ℝ) ≤ t ^ (-(327 / 1292) : ℝ) := by
  have h1 : t ^ (327 / 1292 : ℝ) ≤ ((8 : ℝ) ^ (-(1292 / 327) : ℝ)) ^ (327 / 1292 : ℝ) :=
    Real.rpow_le_rpow ht0.le htle (by norm_num)
  have h2 : ((8 : ℝ) ^ (-(1292 / 327) : ℝ)) ^ (327 / 1292 : ℝ) = (1 : ℝ) / 8 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have htk : t ^ (327 / 1292 : ℝ) ≤ (1 : ℝ) / 8 := h2 ▸ h1
  have hpos : 0 < t ^ (327 / 1292 : ℝ) := Real.rpow_pos_of_pos ht0 _
  rw [Real.rpow_neg ht0.le]
  have hinv := inv_anti₀ hpos htk
  linarith [hinv]

theorem bigM_ge_eight {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → 8 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) (_root_.BoseGases.a v) μ := by
  refine ⟨(8 : ℝ) ^ (-(1292 / 327) : ℝ), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro μ hAdm
  obtain ⟨hμ, htle, -⟩ := hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by
    have : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
    positivity
  rw [bigM_eq ht0]
  exact eight_le_rpow_neg ht0 htle

end Work.BoseFixB2.Arith
