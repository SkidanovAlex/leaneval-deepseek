import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter_half
import Submission.Work.Cusp.collarHeight_mem
import Submission.Work.Cusp.CuspCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-- **The filling branch of the unslabbed collar coordinate**, as a function of a point of the
closed collar source `cuspSourceTop v c δ` (the same term as `cuspCoordMTopUp`, reproduced here so
that the file is self-contained). -/
private def cuspTopUpT (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspSourceTop v c δ}) : a.Mhat :=
  a.incW v (⟨(cuspInvOuter v q.1).1, cuspInvOuter_mem_SqTop v c δ q.1 q.2⟩,
    D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- On the closed collar source the unslabbed collar coordinate is the filling branch. -/
private theorem cuspCoordMTop_eq_cuspTopUpT (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hq : beta (xOf q.1) ≤ q.1 3) :
    cuspCoordMTop a v D c δ q = cuspTopUpT a v D c δ ⟨q.1, ⟨q.2, hq⟩⟩ := by
  unfold cuspCoordMTop cuspTopUpT
  rw [dif_neg (not_lt.mpr hq)]

theorem collarLayer_subset_range_cuspCoordMTop (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (y : a.Torus v) (p : Work.Space.SquarePt) (hp : 1/2 ≤ nrm (p : E2)) :
    ∃ (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2), a.incW v (p, y) ∈ Set.range (cuspCoordMTop a v D c δ) := by
  -- lift the torus point `y` to a real pair `w`
  have hlift : ∀ i : Fin 2, ∃ s : ℝ, (s : AddCircle (1 : ℝ)) = (D.tor y) i :=
    fun i => QuotientAddGroup.mk'_surjective _ _
  choose w0 hw0 using hlift
  set w : E2 := !₂[w0 0, w0 1] with hwdef
  have hw : ∀ i : Fin 2, ((w i : ℝ) : AddCircle (1 : ℝ)) = (D.tor y) i := by
    intro i; fin_cases i <;> simpa [hwdef] using hw0 _
  have hpSq : (p : E2) ∈ Sq := p.2
  have hle1 : nrm (p : E2) ≤ 1 := Work.Space.sqNorm_le_one p
  -- the UHS point of the chart
  set q : E4 := mkE4 (cuspX v (u (p : E2)) w) (collarS v (p : E2) w) with hqdef
  have hq3 : q 3 = collarHeight (nrm (p : E2)) (beta (cuspX v (u (p : E2)) w)) := by
    rw [hqdef, mkE4_apply_three, collarS]
  have hxq : xOf q = cuspX v (u (p : E2)) w := by
    rw [hqdef, xOf_mkE4]
  have hcm := collarHeight_mem (nrm (p : E2)) (beta (cuspX v (u (p : E2)) w)) hp hle1
    (beta_min_le _) (beta_le_max _)
  have hqmem : q ∈ cuspBoxTop v (xOf q) (1/2) := by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [sub_self, abs_zero]; norm_num
    · rw [hq3]; exact hcm.1
    · rw [hq3]; exact lt_of_le_of_lt hcm.2 sJ_lt_sTop
  have hbpos : 0 < beta (cuspX v (u (p : E2)) w) := beta_pos _
  have hblt : beta (cuspX v (u (p : E2)) w) < sJ :=
    lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hbc : beta (xOf q) ≤ q 3 := by
    rw [hxq, hq3]
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · have h := (collarHeight_strictAntiOn _ hbpos hblt) (Set.mem_univ _) (Set.mem_univ _) hlt
      beta_reduce at h
      rw [collarHeight_one _ hbpos] at h
      exact le_of_lt h
    · rw [heq, collarHeight_one _ hbpos]
  have hIO : cuspInvOuter v q = ((p : E2), w) := by
    rw [hqdef]
    exact cuspInvOuter_ThetaOuter_half v (p : E2) w hpSq hp hle1
  refine ⟨xOf q, 1/2, le_refl _, ⟨⟨q, hqmem⟩, ?_⟩⟩
  have hsrc : q ∈ cuspSourceTop v (xOf q) (1/2) := ⟨hqmem, hbc⟩
  rw [cuspCoordMTop_eq_cuspTopUpT a v D (xOf q) (1/2) ⟨q, hqmem⟩ hbc]
  unfold cuspTopUpT
  apply congrArg (a.incW v)
  apply Prod.ext
  · exact Subtype.ext (by simpa using congrArg Prod.fst hIO)
  · have h2 : (fun i : Fin 2 => (((cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ))) = D.tor y := by
      funext i
      have hi : (cuspInvOuter v q).2 i = w i := by
        rw [show (cuspInvOuter v q).2 = w from congrArg Prod.snd hIO]
      rw [hi, hw i]
    rw [h2, Homeomorph.symm_apply_apply]

end Work.Cusp
