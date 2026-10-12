import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBogFS.honestThresholdRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **The scale row of FS §10 at the parameter point `FSParamsView`.**

With `t = μa³` (so `t ≤ 2^{-1000}` and `0 < t ≤ 1`) every scalar of the environment is an
explicit monomial in `t`: `s = t^{1/323}`, `ℓ = t^{-3/646}(μa)^{-1/2}`, `K_L = t^{-21/646}`,
`ε_T = t^{23/1292}`.  Hence

* `(sℓ)^{-1} = √(μa)·t^{1/646} ≤ √(μa)` (since `t ≤ 1`),
* `K_L = t^{-21/646} ≥ 1024` (since `t^{21/646} ≤ 2^{-1000·21/646} ≤ 2^{-10}`),
* `ε_T = t^{23/1292} ≤ 1/2` (since `t^{23/1292} ≤ 2^{-1000·23/1292} ≤ 2^{-1}`);

the last two are exactly the elementary power comparisons `rpow_neg21_ge` and
`rpow_23_le_half` proved in `honestThresholdRow`. -/
theorem scaleRow_of_fsParams {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {E : Work.BoseB7.Q3Env Mode} (hv : Work.BoseB7.FSParamsView E)
    (htε : E.mu * E.aScat ^ 3 ≤ (1 / 2) ^ 1000) :
    (E.s * E.ell)⁻¹ ≤ Real.sqrt (E.mu * E.aScat) ∧ 1024 ≤ E.KL ∧ E.eT ≤ 1 / 2 := by
  -- the diluteness `t = μa³` is `≤ 2^{-1000}`, hence `0 < t ≤ 1`
  have htε' : hv.t ≤ (1 / 2) ^ 1000 := by rw [← hv.mu_eq]; exact htε
  have htpos : 0 < hv.t := hv.t_pos
  have hma : 0 < E.mu * E.aScat := mul_pos (Work.BoseB7.mu_pos E hv) hv.a_pos
  -- the explicit values of the scalars
  have heTv : E.eT = hv.t ^ ((23 : ℝ) / 1292) := by
    rw [hv.eT_eq, Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hKLv : E.KL = hv.t ^ (-(21 / 646 : ℝ)) := by
    have h6 : (Work.BoseBox.fsXp hv.t 6) ^ 2 = Work.BoseBox.fsXp hv.t 12 := by
      rw [Work.BoseBox.fsXp_pow hv.t_pos.le 6 2]
      congr 1
      norm_num
    have h8 : Work.BoseBox.fsXp hv.t (-(3 / 2)) * Work.BoseBox.fsXp hv.t 12
        = Work.BoseBox.fsXp hv.t (21 / 2) := by
      rw [Work.BoseBox.fsXp_mul hv.t_pos (-(3 / 2)) 12]
      congr 1
      norm_num
    have h9 : (Work.BoseBox.fsXp hv.t (21 / 2))⁻¹ = Work.BoseBox.fsXp hv.t (-(21 / 2)) :=
      Work.BoseBox.fsXp_inv hv.t_pos (21 / 2)
    have h10 : Work.BoseBox.fsXp hv.t (-(21 / 2)) = hv.t ^ (-(21 / 646 : ℝ)) := by
      rw [Work.BoseBox.fsXp]
      congr 1
      norm_num
    rw [hv.KL_eq, Work.BoseB7.KL, hv.Kl_eq, hv.d_eq, Real.rpow_neg_one, h6, h8, h9, h10]
  have hS1 : E.s * E.ell
      = (Work.BoseBox.fsXp hv.t 1 * Work.BoseBox.fsXp hv.t (-(3 / 2)))
        * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hv.s_eq, hv.ell_eq, Work.BoseB7.side, hv.Kl_eq]
    ring
  have hS2 : Work.BoseBox.fsXp hv.t 1 * Work.BoseBox.fsXp hv.t (-(3 / 2))
      = hv.t ^ (-(1 / 646 : ℝ)) := by
    rw [Work.BoseBox.fsXp_mul hv.t_pos 1 (-(3 / 2)), Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hS3 : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (E.mu * E.aScat))⁻¹ := by
    rw [Real.rpow_neg hma.le, Real.sqrt_eq_rpow]
  have hSe : E.s * E.ell
      = hv.t ^ (-(1 / 646 : ℝ)) * (Real.sqrt (E.mu * E.aScat))⁻¹ := by
    rw [hS1, hS2, hS3]
  have hA : (E.s * E.ell)⁻¹ = Real.sqrt (E.mu * E.aScat) * hv.t ^ (1 / 646 : ℝ) := by
    rw [hSe, mul_inv, inv_inv, ← Real.rpow_neg hv.t_pos.le, neg_neg]
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- `(sℓ)^{-1} = √(μa)·t^{1/646} ≤ √(μa)` because `t^{1/646} ≤ 1`
    have ht1 : hv.t ≤ 1 := le_trans htε' (pow_le_one₀ (by norm_num) (by norm_num))
    have hle : hv.t ^ (1 / 646 : ℝ) ≤ 1 := Real.rpow_le_one htpos.le ht1 (by norm_num)
    calc (E.s * E.ell)⁻¹ = Real.sqrt (E.mu * E.aScat) * hv.t ^ (1 / 646 : ℝ) := hA
      _ ≤ Real.sqrt (E.mu * E.aScat) * 1 :=
          mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      _ = Real.sqrt (E.mu * E.aScat) := mul_one _
  · -- `1024 ≤ K_L = t^{-21/646}`
    rw [hKLv]
    exact rpow_neg21_ge htpos htε'
  · -- `ε_T = t^{23/1292} ≤ 1/2`
    rw [heTv]
    exact rpow_23_le_half htpos htε'

end Work.BoseBogFS
