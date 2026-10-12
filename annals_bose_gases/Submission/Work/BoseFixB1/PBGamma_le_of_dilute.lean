import ChallengeDeps
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- **The `fsXp` arithmetic of the `PBΓ` gate at an arbitrary bound.**  For `0 < t` and
`t ≤ c^{646/287}` one has

`K_B³·t^{1/2} = (fsXp t (−6))³·t^{1/2} = t^{287/646} ≤ c`,

since `fsXp t (−6) = t^{−6/323}`, so `(fsXp t (−6))³ = t^{−18/323}` and the product is
`t^{−18/323 + 1/2} = t^{287/646}`, which is `≤ (c^{646/287})^{287/646} = c`.

This is the general-bound form of `fsXp_neg_six_cube_mul_sqrt_le_one` (the case `c = 1`),
which is what the `PBΓ` gate needs when the prescribed constant is any `c > 0`: the
threshold `ε₀` must then be shrunk to `c^{646/287}`. -/
lemma fsXp_neg_six_cube_mul_sqrt_le {t c : ℝ} (hc : 0 < c) (ht0 : 0 < t)
    (htc : t ≤ c ^ (646 / 287 : ℝ)) :
    (Work.BoseBox.fsXp t (-6)) ^ 3 * t ^ (1 / 2 : ℝ) ≤ c := by
  have hK3 : (Work.BoseBox.fsXp t (-6)) ^ 3 = t ^ ((-(18) : ℝ) / 323) := by
    rw [Work.BoseBox.fsXp, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hprod : (Work.BoseBox.fsXp t (-6)) ^ 3 * t ^ (1 / 2 : ℝ) = t ^ (287 / 646 : ℝ) := by
    rw [hK3, ← Real.rpow_add ht0]
    norm_num
  rw [hprod]
  calc t ^ (287 / 646 : ℝ) ≤ (c ^ (646 / 287 : ℝ)) ^ (287 / 646 : ℝ) :=
        Real.rpow_le_rpow ht0.le htc (by norm_num)
    _ = c := by
        rw [← Real.rpow_mul hc.le]
        norm_num

theorem PBGamma_le_of_dilute {v : EuclideanSpace ℝ (Fin 3) → ℝ} {c : ℝ} (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      Work.BoseFixB1B.PBΓ v μ ≤ c := by
  refine ⟨min 1 (c ^ (646 / 287 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos hc (646 / 287)), fun μ hAdm => ?_⟩
  have hμ : 0 < μ := adm_mu_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := adm_a_pos hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos ha 3)
  have htc : μ * (_root_.BoseGases.a v) ^ 3 ≤ c ^ (646 / 287 : ℝ) :=
    le_trans (adm_dilute hAdm) (min_le_right 1 _)
  have hgoal : Work.BoseFixB1B.PBΓ v μ
      = (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-6)) ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := by
    simp only [Work.BoseFixB1B.PBΓ, Work.BoseFixB1B.PBKB, Work.FockBridge.dlGamma,
      Work.BoseFixB1.paramsAt_eq_fsParams, Work.BoseBox.fsParams]
  rw [hgoal]
  exact fsXp_neg_six_cube_mul_sqrt_le hc ht0 htc

end Work.BoseFixB1
