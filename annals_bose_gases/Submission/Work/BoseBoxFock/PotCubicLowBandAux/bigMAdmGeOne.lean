import ChallengeDeps
import Submission.Work.BoseBox.Nodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.bigMAdmGeOne`

The FS matrix-localisation window `𝓜 = bigM (paramsAt μ (a v)) (a v) μ` of
`eq:DefM` is at least `1` as soon as the diluteness `t = μ(a v)³` is at most `1`.

At FS's parameters (`fsParams`, `BoseBox/Basic.lean`)

    𝓜 = K_M · t^{-1/4} = t^{-1/323} · t^{-1/4} = t^{-(1/323 + 1/4)} = t^{-327/1292},

and `0 < t ≤ 1` with a negative exponent gives `t^{-327/1292} ≥ 1`.  Note the
hypothesis `μ(a v)³ ≤ 1` (not an `ε₀`-threshold): the conclusion `1 ≤ 𝓜` is
exactly the trivial half of the window arithmetic, and holds without any
diluteness cap. -/

namespace Work.BoseBoxFock.PotCubicLowBandAux

/-- At FS's parameters the window is the monomial `(μa³)^{-327/1292}`. -/
lemma bigM_paramsAt_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (ht0 : 0 < μ * (BoseGases.a v) ^ 3) :
    Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
      = (μ * (BoseGases.a v) ^ 3) ^ (-(327 / 1292) : ℝ) := by
  rw [Work.BoseBox.bigM]
  have hK : (Work.BoseBox.paramsAt μ (BoseGases.a v)).KM
      = (μ * (BoseGases.a v) ^ 3) ^ ((-1) / 323 : ℝ) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [hK, ← Real.rpow_add ht0]
  norm_num

/-- A negative power of a number in `(0,1]` is at least `1`. -/
lemma one_le_rpow_neg_of_le_one {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    1 ≤ t ^ (-c) := by
  rw [Real.rpow_neg ht0.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos ht0 c)).mpr (Real.rpow_le_one ht0.le ht hc)

theorem bigMAdmGeOne {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < BoseGases.a v) {μ : ℝ}
    (hμ : 0 < μ) (ht : μ * BoseGases.a v ^ 3 ≤ 1) :
    1 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ := by
  have hav3 : 0 < (BoseGases.a v) ^ 3 := by positivity
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := mul_pos hμ hav3
  rw [bigM_paramsAt_eq ht0]
  exact one_le_rpow_neg_of_le_one ht0 ht (by norm_num)

end Work.BoseBoxFock.PotCubicLowBandAux
