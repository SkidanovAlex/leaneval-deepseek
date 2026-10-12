import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.eta_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseC3QAll

theorem lille_threshold (K₀ : ℝ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → 96 * max K₀ 0 * E.lille ≤ 1 := by
  set M := max K₀ 0 with hM
  have hMnn : 0 ≤ M := le_max_right K₀ 0
  have hden : 0 < 96 * M + 1 := by linarith
  have hbase_pos : 0 < 1 / (96 * M + 1) := div_pos one_pos hden
  refine ⟨(1 / (96 * M + 1)) ^ (646 / 97 : ℝ), Real.rpow_pos_of_pos hbase_pos _, ?_⟩
  intro Mode _ _ E hv htle
  have hlille : E.lille = hv.t ^ (97 / 646 : ℝ) := by
    rw [Work.BoseB7.lille_val E hv]
    simp only [Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hkey : ((1 / (96 * M + 1)) ^ (646 / 97 : ℝ)) ^ (97 / 646 : ℝ) = 1 / (96 * M + 1) := by
    rw [(Real.rpow_mul hbase_pos.le (646 / 97) (97 / 646)).symm]
    rw [show (646 / 97 : ℝ) * (97 / 646) = 1 by norm_num, Real.rpow_one]
  have hstep : E.lille ≤ 1 / (96 * M + 1) := by
    rw [hlille, ← hkey]
    exact Real.rpow_le_rpow hv.t_pos.le htle (by norm_num)
  have h96 : 0 ≤ 96 * M := by linarith
  calc 96 * max K₀ 0 * E.lille = 96 * M * E.lille := by rw [hM]
    _ ≤ 96 * M * (1 / (96 * M + 1)) := mul_le_mul_of_nonneg_left hstep h96
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one hden]; linarith

end Work.BoseC3QAll
