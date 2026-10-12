import ChallengeDeps
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

/-- At FS's parameter choice (`paramsAt μ (a v) = fsParams (μ(a v)³)`, with
`K_B = X^{-6}`, `K_ℓ = X^{-3/2}` and `X = (μa³)^{1/323}`) the window factor of
`wbEps` collapses to a single power of the diluteness,

    K_B^{3/2} · K_ℓ · (μa³)^{1/4} = (μa³)^{281/1292},

with the **positive** exponent `281/1292` (`-9/323 - 3/646 + 1/4 = 281/1292`). -/
private lemma wbEps_eq_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (ht : 0 < μ * (_root_.BoseGases.a v) ^ 3) :
    Work.BoseFixB1.wbEps v μ = (μ * (_root_.BoseGases.a v) ^ 3) ^ (281 / 1292 : ℝ) := by
  rw [Work.BoseFixB1.wbEps]
  rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (281 / 1292 : ℝ) from ?_]
  · simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    rw [Work.BoseBox.fsXp_rpow ht.le (-6) (3 / 2)]
    rw [show (-6 : ℝ) * (3 / 2) = -9 by norm_num]
    rw [Work.BoseBox.fsXp_mul ht (-9) (-(3 / 2))]
    rw [show (-9 : ℝ) + -(3 / 2) = -(21 / 2) by norm_num]
    simp only [Work.BoseBox.fsXp]
    rw [show -((21 : ℝ) / 2) / 323 = -(21 / 646) by norm_num]
    rw [← Real.rpow_add ht]
    norm_num

theorem eps_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      Work.BoseFixB1.wbEps v μ ≤ 1 / 2 := by
  refine ⟨(1 / 2 : ℝ) ^ (1292 / 281 : ℝ), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro μ hμ hle
  have hav3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ hav3
  rw [wbEps_eq_rpow ht]
  have hstep : (μ * (_root_.BoseGases.a v) ^ 3) ^ (281 / 1292 : ℝ)
      ≤ ((1 / 2 : ℝ) ^ (1292 / 281 : ℝ)) ^ (281 / 1292 : ℝ) :=
    Real.rpow_le_rpow ht.le hle (by norm_num)
  have hrhs : ((1 / 2 : ℝ) ^ (1292 / 281 : ℝ)) ^ (281 / 1292 : ℝ) = 1 / 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (1292 / 281 : ℝ) * (281 / 1292) = 1 by norm_num, Real.rpow_one]
  rw [hrhs] at hstep
  exact hstep

end Work.BoseFixB1.WB
