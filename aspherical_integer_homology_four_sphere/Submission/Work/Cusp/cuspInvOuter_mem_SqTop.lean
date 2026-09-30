/-
# The layer parameter of the unslabbed collar chart lies in `(1/4, 1]`

For a point `q = (x,s)` of the *unslabbed* collar source `cuspSourceTop v c δ` (the box of side
`2δ` with height in `(s₁, sTop)`, on or above the ceiling) the inverse outer chart `cuspInvOuter v`
recovers

  `(t • bndOfU (outerU v x), outerY v x)`,  `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`.

Writing `A = log s − log β(x) ≥ 0` (the point is on or above the ceiling) and
`J = log s_J − log β(x) > 0` (because `β(x) ≤ β_max < s_J`), we have `t = 1 − A/(2J)`.  Hence

* `t ≤ 1` is `A ≥ 0`;
* `t > layerLo = 1/4` is `3J > 2A`, equivalently `log (s² β(x)) < log (s_J³)`, i.e.
  `s² β(x) < s_J³` — which follows from `s < sTop`, `β(x) ≤ β_max` and
  `β_max · sTop² < s_J³` (`Work.Cusp.betaMax_mul_sTop_sq_lt_sJ_cu`).

The second bound is what makes the recovered point lie in the *collar* `{layerLo < ‖·‖∞ ≤ 1}` of the
filling square — in particular in `Sq` itself and bounded away from the core, so that the layer
chart `layerPtI` is an open embedding.  (For the slabbed family one only gets `t ≥ 0` from its
window `(s₁, s_J)`, and the corner directions `u(p) ∈ ℤ` are not covered at all.)
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.cuspX_outerU_outerY

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The recovered layer parameter of the unslabbed collar chart lies in `(layerLo, 1]`.** -/
theorem cuspInvOuter_nrm_Top (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) :
    layerLo < nrm (cuspInvOuter v q).1 ∧ nrm (cuspInvOuter v q).1 ≤ 1 := by
  obtain ⟨hbox, hbeta⟩ := hq
  obtain ⟨_hx, hs1, hlt⟩ := hbox
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hs_pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hsJpos : 0 < sJ := Real.exp_pos _
  -- the logarithmic comparisons
  have hlogb_le_logs : Real.log (beta (xOf q)) ≤ Real.log (q 3) := Real.log_le_log hbpos hbeta
  have hDpos : 0 < Real.log sJ - Real.log (beta (xOf q)) := by
    linarith [Real.log_lt_log hbpos (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)]
  have hA0 : 0 ≤ Real.log (q 3) - Real.log (beta (xOf q)) := by linarith
  -- the chart inverse is a scalar multiple of a boundary point
  have hunfold : (cuspInvOuter v q).1 =
      (1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ))) • bndOfU (outerU v (xOf q)) := by
    simp only [cuspInvOuter, xOf]
  -- rewrite the scalar in the equivalent decreasing form `1 - A / (2 J)`
  have hmerge : 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ))
      = 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log sJ - Real.log (beta (xOf q)))) := by
    have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q)))) := by ring
    rw [hden, div_neg]
    ring
  have h2Jpos : 0 < 2 * (Real.log sJ - Real.log (beta (xOf q))) := by linarith
  -- `t ≤ 1`
  have hT_le : 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) ≤ 1 := by
    have h : 0 ≤ (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) := div_nonneg hA0 (le_of_lt h2Jpos)
    linarith
  -- `t > 1/4`, from `q 3 ^ 2 * β(x) < sTop ^ 2 * β_max < s_J ^ 3`
  have hprod : q 3 ^ 2 * beta (xOf q) < sJ ^ 3 := by
    have h1 : q 3 ^ 2 * beta (xOf q) < sTop ^ 2 * beta (xOf q) :=
      mul_lt_mul_of_pos_right (by nlinarith [hs_pos, hlt]) hbpos
    have h2 : sTop ^ 2 * beta (xOf q) ≤ sTop ^ 2 * betaMax :=
      mul_le_mul_of_nonneg_left (beta_le_max _) (by positivity)
    linarith [betaMax_mul_sTop_sq_lt_sJ_cu]
  have hlogprod : 2 * Real.log (q 3) + Real.log (beta (xOf q)) < 3 * Real.log sJ := by
    have h := Real.log_lt_log (by positivity) hprod
    rw [Real.log_mul (by positivity) (ne_of_gt hbpos), Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hlt23 : 2 * (Real.log (q 3) - Real.log (beta (xOf q)))
      < 3 * (Real.log sJ - Real.log (beta (xOf q))) := by linarith
  have hT_gt : layerLo < 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) := by
    have h3 : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) < 3/4 := by
      rw [div_lt_iff₀ h2Jpos]
      linarith
    rw [layerLo]
    linarith
  -- the sup norm of the recovered point is `t`
  have hT_pos : 0 < 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) :=
    lt_trans (by norm_num [layerLo]) hT_gt
  have hnrm : nrm (cuspInvOuter v q).1
      = 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log sJ - Real.log (beta (xOf q)))) := by
    rw [hunfold, hmerge, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos hT_pos]
  rw [hnrm]
  exact ⟨hT_gt, hT_le⟩

/-- **The recovered point of the unslabbed collar chart lies in the collar stratum of the square**
(the pair of bounds of `cuspInvOuter_nrm_Top`). -/
theorem cuspInvOuter_mem_cuspStratumTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) : (cuspInvOuter v q).1 ∈ Sq := by
  obtain ⟨-, hle⟩ := cuspInvOuter_nrm_Top v c δ q hq
  exact ⟨le_trans (abs_le_nrm _ 0) hle, le_trans (abs_le_nrm _ 1) hle⟩

/-- **The recovered point of the unslabbed collar chart lies in the filling square.** -/
theorem cuspInvOuter_mem_SqTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) : (cuspInvOuter v q).1 ∈ Sq :=
  cuspInvOuter_mem_cuspStratumTop v c δ q hq

end Work.Cusp
