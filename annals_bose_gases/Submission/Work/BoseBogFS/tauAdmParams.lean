import ChallengeDeps
import Submission.Work.BoseBogFS.existsAdmRegime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The diluteness threshold forcing FS's regularisation gap below `1/2`:
`fsXp t (23/4) = t^{23/1292} ≤ ((1/2)^{1292/23})^{23/1292} = 1/2` whenever
`0 < t ≤ (1/2)^{1292/23}` (the exponents multiply to `1`). -/
lemma fsXp_23_4_le_half {t : ℝ} (ht : 0 < t)
    (htle : t ≤ (1 / 2 : ℝ) ^ ((1292 : ℝ) / 23)) :
    Work.BoseBox.fsXp t (23 / 4) ≤ 1 / 2 := by
  have h := Real.rpow_le_rpow ht.le htle (by norm_num : (0 : ℝ) ≤ (23 : ℝ) / 1292)
  have hbase : ((1 / 2 : ℝ) ^ ((1292 : ℝ) / 23)) ^ ((23 : ℝ) / 1292) = 1 / 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
      show ((1292 : ℝ) / 23) * ((23 : ℝ) / 1292) = 1 by norm_num, Real.rpow_one]
  rw [hbase] at h
  rwa [Work.BoseBox.fsXp, show ((23 : ℝ) / 4) / 323 = (23 : ℝ) / 1292 by norm_num]

theorem tauAdmParams {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ∧
        0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ∧
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 ∧
            0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ∧
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2 ∧
                0 < Work.BoseFixR.ell v μ := by
  refine ⟨min 1 ((1 / 2 : ℝ) ^ ((1292 : ℝ) / 23)),
    lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro μ hAdm
  obtain ⟨hμ, hdil, _⟩ := hAdm
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hdil (min_le_left _ _)
  have htc : μ * (_root_.BoseGases.a v) ^ 3 ≤ (1 / 2 : ℝ) ^ ((1292 : ℝ) / 23) :=
    le_trans hdil (min_le_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using
      Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 1) ht
  · simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using
      Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 6) ht
  · simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using
      Work.BoseBox.fsXp_le_one (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 6) ht ht1
        (by norm_num)
  · simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using
      le_of_lt (Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 23 / 4) ht)
  · simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using
      fsXp_23_4_le_half ht htc
  · rw [Work.BoseFixR.ell_eq]
    simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide]
    refine mul_pos ?_ (Real.rpow_pos_of_pos (mul_pos hμ hav) _)
    simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using
      Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := -(3 / 2)) ht

end Work.BoseBogFS
