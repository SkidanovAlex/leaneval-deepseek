/-
# The layer parameter of the inverse outer cusp chart lies in the collar stratum

For `q ∈ cuspSource v c δ` the inverse outer chart of the filling piece (`Work.Cusp.cuspInvOuter`)
reports the layer parameter `‖p‖∞` of the point of the square `Sq` it recovers.  This file shows
that this layer parameter lies in the collar stratum `cuspStratum = {1/2 < ‖p‖∞ ≤ 1}`.

Concretely `cuspInvOuter v q = (t • bndOfU (outerU v x), outerY v x)` with `x = xOf q`,
`b = β x` and

`t = 1 + (log (q 3) − log b) / (2 (log b − log s_J))`.

Since `nrm (bndOfU u) = 1` (`nrm_bndOfU`) and `nrm` is homogeneous (`nrm_smul`), we have
`nrm (cuspInvOuter v q).1 = |t| = t`; it remains to bound `t`.

Membership `q ∈ cuspSource v c δ` gives `s₁ < q 3 < s_J` and the ceiling bound `β x ≤ q 3`, so

* `log b < log s_J`, `log b ≤ log (q 3) < log s_J` and `b > 0` (`beta_pos`, `beta_le_max`,
  `betaMax_lt_sJ`, `s1_lt_betaMin`);

the denominator `2 (log b − log s_J)` is negative, while the numerator `log (q 3) − log b ≥ 0`, so
the correction term is `≤ 0` and `t ≤ 1`; and the numerator is strictly smaller than
`log s_J − log b = −(log b − log s_J)`, which gives `t > 1/2`.  Hence `t ∈ (1/2, 1]` and
`(cuspInvOuter v q).1 ∈ cuspStratum`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.s1_lt_betaMin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

theorem cuspInvOuter_mem_cuspStratum (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSource v c δ) : (cuspInvOuter v q).1 ∈ cuspStratum := by
  obtain ⟨hbox, hceil⟩ := hq
  obtain ⟨-, hs1, hsJ, -, -⟩ := hbox
  set e : ℝ := 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
      (2 * (Real.log (beta (xOf q)) - Real.log sJ)) with he
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hb_lt_sJ : beta (xOf q) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1] : (0:ℝ) < s1) hs1
  have hlogb_lt : Real.log (beta (xOf q)) < Real.log sJ := Real.log_lt_log hbpos hb_lt_sJ
  have hlog_le : Real.log (beta (xOf q)) ≤ Real.log (q 3) := Real.log_le_log hbpos hceil
  have hlog3_lt : Real.log (q 3) < Real.log sJ := Real.log_lt_log hq3pos hsJ
  have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ) < 0 := by linarith
  have hA : 0 ≤ Real.log (q 3) - Real.log (beta (xOf q)) := by linarith
  have he_le : e ≤ 1 := by
    rw [he]
    have : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hA (le_of_lt hden)
    linarith
  have he_gt : 1/2 < e := by
    rw [he]
    have hhalf : (-1:ℝ)/2 < (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ)) := by
      rw [lt_div_iff_of_neg hden]
      have hrr : (-1:ℝ)/2 * (2 * (Real.log (beta (xOf q)) - Real.log sJ))
          = Real.log sJ - Real.log (beta (xOf q)) := by ring
      rw [hrr]
      linarith
    linarith
  have he_pos : 0 < e := by linarith
  change 1 / 2 < nrm ((cuspInvOuter v q).1) ∧ nrm ((cuspInvOuter v q).1) ≤ 1
  have hpe : (cuspInvOuter v q).1 = e • bndOfU (outerU v (xOf q)) := by
    rw [he]; rfl
  rw [hpe, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos he_pos]
  exact ⟨he_gt, he_le⟩

end Work.Cusp
