import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The `log T` row at the honest kernel data.  With `D = dil v μ`, `L = log D⁻¹`, `B = D^{1/1292}`
and `ε = lhyEpsX v R μ`, the honest momentum cutoff is `T = 10⁶(1+L)/ε`, and using `log(10⁶) ≤ 54`,
`log(1+L) ≤ L` and `log ε ≥ log B = -(1/1292)L` one gets `log T ≤ 54 + (1293/1292)L`. -/
lemma bogTLogLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ ρ : ℝ}
    (hCore : Work.BoseBogFS.Core v R μ ρ) :
    Real.log (Work.BoseBogFS.bogT v R μ) ≤ 54 + (1293 / 1292) * Work.BoseBogFS.bogL v μ := by
  have hL0 : 0 ≤ bogL v μ := hCore.hL0
  have hD0 : 0 < Work.BoseFixR.dil v μ := hCore.hD0
  -- the error `ε` is strictly positive (it dominates `D^{23/1292} > 0`)
  have hD23 : 0 < (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := Real.rpow_pos_of_pos hD0 _
  have hεpos : 0 < lhyEpsX v R μ := lt_of_lt_of_le hD23 hCore.hE1
  have hnum : 0 < (10 : ℝ) ^ 6 * (1 + bogL v μ) := by positivity
  -- `log D = -L`
  have hlogD : Real.log (Work.BoseFixR.dil v μ) = - bogL v μ := by
    rw [bogL, ← Real.log_inv, one_div, inv_inv]
  -- `ε ≥ D^{1/1292}`, hence `log ε ≥ -(1/1292)L`
  have hBpos : 0 < (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := Real.rpow_pos_of_pos hD0 _
  have hle1 : (1 : ℝ) ≤ 1 + 156 / 323 * bogL v μ := by
    have : 0 ≤ 156 / 323 * bogL v μ := by positivity
    linarith
  have hBlow : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≤ lhyEpsX v R μ := by
    have h := mul_le_mul_of_nonneg_left hle1 hBpos.le
    linarith [h, hCore.hE3]
  have hlogε_ge : -((1 : ℝ) / 1292) * bogL v μ ≤ Real.log (lhyEpsX v R μ) := by
    have h : Real.log ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292))
        ≤ Real.log (lhyEpsX v R μ) := Real.log_le_log hBpos hBlow
    rw [Real.log_rpow hD0, hlogD] at h
    linarith [h]
  have hneg : - Real.log (lhyEpsX v R μ) ≤ ((1 : ℝ) / 1292) * bogL v μ := by linarith
  -- `log(10⁶) ≤ 54`
  have hlog10 : Real.log (1000000 : ℝ) ≤ 54 := by
    have h : Real.log ((10 : ℝ) ^ 6) ≤ 54 := by
      rw [Real.log_pow]
      have h' : Real.log (10 : ℝ) ≤ 9 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
        linarith
      push_cast
      nlinarith
    rwa [show ((10 : ℝ) ^ 6) = (1000000 : ℝ) by norm_num] at h
  -- `log(1+L) ≤ L`
  have hlog1L : Real.log (1 + bogL v μ) ≤ bogL v μ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + bogL v μ)
    linarith
  have hT : Real.log (bogT v R μ)
      = Real.log ((10 : ℝ) ^ 6) + Real.log (1 + bogL v μ) - Real.log (lhyEpsX v R μ) := by
    rw [hCore.hTdef, Real.log_div (ne_of_gt hnum) (ne_of_gt hεpos),
        Real.log_mul (by positivity) (by linarith : (1 + bogL v μ) ≠ 0)]
  rw [hT, show ((10 : ℝ) ^ 6) = (1000000 : ℝ) by norm_num]
  have hsum : Real.log (1000000 : ℝ) + Real.log (1 + bogL v μ) ≤ 54 + bogL v μ :=
    add_le_add hlog10 hlog1L
  have key : Real.log (1000000 : ℝ) + Real.log (1 + bogL v μ) - Real.log (lhyEpsX v R μ)
      ≤ 54 + bogL v μ + (1 / 1292) * bogL v μ := by linarith [hsum, hneg]
  have harith : (54 : ℝ) + bogL v μ + (1 / 1292) * bogL v μ
      = 54 + (1293 / 1292) * bogL v μ := by ring
  rw [harith] at key
  exact key

end Work.BoseBogFS
