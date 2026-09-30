import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.cuspInvOuter_heightTop
import Submission.Work.Cusp.beta_cuspX_fract
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.CuspCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem cuspTopInv_apply_cuspTopF (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q : {q : E4 // q ∈ cuspSourceTop v c δ}) :
    cuspTopInv v (cuspAnchor v c) (cuspTopF v c δ hδ q) = q.1 := by
  obtain ⟨hbox, hbetale⟩ := q.2
  obtain ⟨hside, hs1, hlt⟩ := hbox
  have hq3pos : 0 < q.1 3 := lt_trans (by norm_num [s1]) hs1
  have hbpos : 0 < beta (xOf q.1) := beta_pos _
  have hb_lt_sJ : beta (xOf q.1) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hne : Real.log (beta (xOf q.1)) ≠ Real.log sJ :=
    ne_of_lt (Real.log_lt_log hbpos hb_lt_sJ)
  set T : ℝ := 1 + (Real.log (q.1 3) - Real.log (beta (xOf q.1))) /
      (2 * (Real.log (beta (xOf q.1)) - Real.log sJ)) with hTdef
  -- the explicit form of the recovered layer parameter
  have hunfold : (cuspInvOuter v q.1).1 = T • bndOfU (outerU v (xOf q.1)) := by
    rw [hTdef]; rfl
  -- the recovered layer parameter is positive
  have hprod : q.1 3 * beta (xOf q.1) < sJ ^ 2 := by
    have h1 : q.1 3 * beta (xOf q.1) < sTop * beta (xOf q.1) :=
      mul_lt_mul_of_pos_right hlt hbpos
    have h2 : sTop * beta (xOf q.1) ≤ sTop * betaMax :=
      mul_le_mul_of_nonneg_left (beta_le_max _) (le_of_lt sTop_pos)
    have h3 : sTop * betaMax < sJ ^ 2 := by
      rw [mul_comm]; exact betaMax_mul_sTop_lt_sJ_sq
    linarith
  have h2J : 0 < 2 * (Real.log sJ - Real.log (beta (xOf q.1))) := by
    linarith [Real.log_lt_log hbpos hb_lt_sJ]
  have hTrepr : T = 1 - (Real.log (q.1 3) - Real.log (beta (xOf q.1))) /
      (2 * (Real.log sJ - Real.log (beta (xOf q.1)))) := by
    rw [hTdef]
    have hden : 2 * (Real.log (beta (xOf q.1)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q.1)))) := by ring
    rw [hden, div_neg]; ring
  have hTpos : 0 < T := by
    rw [hTrepr, sub_pos, div_lt_one h2J]
    have h := Real.log_lt_log (mul_pos hq3pos hbpos) hprod
    rw [Real.log_mul (ne_of_gt hq3pos) (ne_of_gt hbpos), Real.log_pow] at h
    push_cast at h
    linarith
  have hnrm : nrm (cuspInvOuter v q.1).1 = T := by
    rw [hunfold, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos hTpos]
  -- the height round trip
  have hh : collarHeight (nrm (cuspInvOuter v q.1).1) (beta (xOf q.1)) = q.1 3 := by
    rw [hnrm, hTdef]
    exact collarHeight_of_log _ _ hq3pos hne
  -- the point is reassembled from its coordinates
  have hkey : cuspTopInv v (cuspAnchor v c) (cuspTopF v c δ hδ q)
      = mkE4 (cuspX v (outerU v (xOf q.1)) (outerY v (xOf q.1)))
          (collarHeight (nrm (cuspInvOuter v q.1).1)
            (beta (cuspX v (outerU v (xOf q.1)) (outerY v (xOf q.1))))) := rfl
  rw [hkey, cuspX_outerU_outerY v (xOf q.1), hh, mkE4_xOf_three]

end Work.Cusp
