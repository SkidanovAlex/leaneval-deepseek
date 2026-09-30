import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- On the source of the cusp chart the recovered layer parameter
`t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))` lies in `[1/2, 1]`: the height `s = q 3`
satisfies `β(x) ≤ s < s_J`, so `log s − log β` lies between `0` and `log s_J − log β > 0`, and `t`
is `1` minus half of the ratio.  In particular `t ∈ [0,1]`, which is what makes
`t • bndOfU ·` land in the square `Sq`. -/
theorem cuspInvOuter_mem_Sq (v : Fin 5) (c : E3) (δ : ℝ) (q : E4) (hq : q ∈ cuspSource v c δ) :
    (cuspInvOuter v q).1 ∈ Sq := by
  obtain ⟨hbox, hbeta⟩ := hq
  obtain ⟨_hx, hs1, hlt, _hu0, _hu1⟩ := hbox
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hs1pos : (0 : ℝ) < s1 := by norm_num [s1]
  have hs_pos : 0 < q 3 := lt_trans hs1pos hs1
  -- the two logarithmic comparisons coming from `β(x) ≤ q 3 < s_J`
  have hlogb_le_logs : Real.log (beta (xOf q)) ≤ Real.log (q 3) := Real.log_le_log hbpos hbeta
  have hlogs_lt_logsJ : Real.log (q 3) < Real.log sJ := Real.log_lt_log hs_pos hlt
  have hDpos : 0 < Real.log sJ - Real.log (beta (xOf q)) := by linarith
  have hA0 : 0 ≤ Real.log (q 3) - Real.log (beta (xOf q)) := by linarith
  have hAD : Real.log (q 3) - Real.log (beta (xOf q))
      ≤ Real.log sJ - Real.log (beta (xOf q)) := by linarith
  -- the chart inverse is a scalar multiple of a boundary point
  have hunfold : (cuspInvOuter v q).1 =
      (1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ))) • bndOfU (outerU v (xOf q)) := by
    simp only [cuspInvOuter, xOf]
  -- rewrite the scalar in the equivalent decreasing form `1 - A / (2 D)`
  have hmerge : 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ))
      = 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log sJ - Real.log (beta (xOf q)))) := by
    have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q)))) := by ring
    rw [hden, div_neg]
    ring
  have h2Dpos : 0 < 2 * (Real.log sJ - Real.log (beta (xOf q))) := by linarith
  have hT_le : 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) ≤ 1 := by
    have h : 0 ≤ (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) := div_nonneg hA0 (le_of_lt h2Dpos)
    linarith
  have hT_ge : 0 ≤ 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) := by
    have h : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) ≤ 1 := by
      rw [div_le_iff₀ h2Dpos]
      linarith
    linarith
  -- the sup norm of the recovered point is `|t| ≤ 1`
  have hnrm : nrm (cuspInvOuter v q).1 ≤ 1 := by
    rw [hunfold, hmerge, nrm_smul, nrm_bndOfU]
    have habs : |1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q))))| ≤ 1 :=
      abs_le.mpr ⟨by linarith, hT_le⟩
    linarith
  change |(cuspInvOuter v q).1 0| ≤ 1 ∧ |(cuspInvOuter v q).1 1| ≤ 1
  exact ⟨le_trans (abs_le_nrm _ 0) hnrm, le_trans (abs_le_nrm _ 1) hnrm⟩

end Work.Cusp
