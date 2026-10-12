import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The inverse-`c₂` row.  `c₂ = (2 d s ℓ √(ρa))⁻¹ = ½(K_ℓ d s)⁻¹√(μ/ρ)` with `K_ℓ d s = D^{11/646} ≤ 1`
and `√(μ/ρ) ≥ √(10/11) > 1/2` (since `ρ ≤ 11/10 μ`), so `c₂ ≥ 1/4` and `log(1/c₂) ≤ log 4 ≤ 3`. -/
lemma bogC2InvLogLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hCore : Work.BoseBogFS.Core v R μ ρ) :
    Real.log (1 / Work.BoseBogFS.bogC2 v ρ μ) ≤ 3 := by
  have hμ := hCore.hμ
  have hρ0 := hCore.hρ0
  have hD0 := hCore.hD0
  have hD1 := hCore.hD1
  -- `K = K_ℓ d s` in the two orderings, and its monomial form `D^{11/646}`.
  set K : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hKdef
  have hK_eq : K = Work.BoseFixR.dil v μ ^ ((11 : ℝ) / 646) := by
    rw [hKdef]
    have h := Work.BoseBogFS.dsKl_eq v μ hD0
    rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl from by ring]
    exact h
  have hKpos : 0 < K := by rw [hK_eq]; exact Real.rpow_pos_of_pos hD0 _
  have hKle : K ≤ 1 := by
    rw [hK_eq]; exact Real.rpow_le_one hD0.le hD1 (by norm_num)
  have hKinv : 1 ≤ K⁻¹ := (one_le_inv₀ hKpos).mpr hKle
  -- the closed form of `c₂`
  have hc2' : Work.BoseBogFS.bogC2 v ρ μ = (1 / 2) * K⁻¹ * Real.sqrt (μ / ρ) := by
    rw [Work.BoseBogFS.bogC2_eq v ρ μ hav hμ hρ0]
  -- `√(μ/ρ) ≥ 1/2` from `ρ ≤ 11/10 μ`
  have hsq : (1 : ℝ) / 2 ≤ Real.sqrt (μ / ρ) := by
    have h1 : (1 : ℝ) / 4 ≤ μ / ρ := by
      rw [le_div_iff₀ hρ0]
      nlinarith [hCore.hρhi]
    calc (1 : ℝ) / 2 = Real.sqrt ((1 : ℝ) / 4) := by
          rw [show ((1 : ℝ) / 4) = ((1 : ℝ) / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (μ / ρ) := Real.sqrt_le_sqrt h1
  have hc2ge : (1 : ℝ) / 4 ≤ Work.BoseBogFS.bogC2 v ρ μ := by
    rw [hc2']
    have h1 : (1 : ℝ) / 2 * 1 * (1 / 2) ≤ (1 / 2) * K⁻¹ * Real.sqrt (μ / ρ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hKinv (by norm_num)
      · exact hsq
      · norm_num
      · exact mul_nonneg (by norm_num) (le_trans (by norm_num) hKinv)
    linarith [h1]
  have hle : (1 : ℝ) / Work.BoseBogFS.bogC2 v ρ μ ≤ 4 := by
    have := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 4 by norm_num) hc2ge
    simpa using this
  have hlog := Real.log_le_log (by positivity : 0 < 1 / Work.BoseBogFS.bogC2 v ρ μ) hle
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  linarith

end Work.BoseBogFS
