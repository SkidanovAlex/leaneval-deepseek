import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.cuspInvOuter_continuousOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

attribute [local fun_prop] outerU_continuous

/-- The unslabbed collar source lies in the open half space `{0 < q 3}` on which the inverse of the
outer chart is continuous: its height window starts at `s₁ = 11/10 > 0`. -/
theorem cuspSourceTop_subset_pos (v : Fin 5) (c : E3) (δ : ℝ) :
    cuspSourceTop v c δ ⊆ {q : E4 | 0 < q 3} := by
  rintro q ⟨⟨-, hs1, -⟩, -⟩
  simpa using lt_trans (by norm_num [s1] : (0:ℝ) < s1) hs1

theorem continuous_cuspTopF (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Continuous (cuspTopF v c δ hδ) := by
  have hxOf : Continuous xOf := by unfold xOf; fun_prop
  have hU : Continuous (fun q : {q : E4 // q ∈ cuspSourceTop v c δ} => outerU v (xOf q.1)) :=
    (outerU_continuous v).comp (hxOf.comp continuous_subtype_val)
  have hIO : Continuous (fun q : {q : E4 // q ∈ cuspSourceTop v c δ} => cuspInvOuter v q.1) := by
    have h := ((cuspInvOuter_continuousOn v).mono (cuspSourceTop_subset_pos v c δ)).domRestrict
    rw [Set.domRestrict_eq] at h
    exact h
  have hn : Continuous (fun q : {q : E4 // q ∈ cuspSourceTop v c δ} =>
      nrm (cuspInvOuter v q.1).1) :=
    nrm_continuous.comp hIO.fst
  have hg : Continuous (fun q : {q : E4 // q ∈ cuspSourceTop v c δ} =>
      (outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1)) := hU.prodMk hn
  have hfst : Continuous (fun q : {q : E4 // q ∈ cuspSourceTop v c δ} =>
      (⟨(outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1),
        ⟨outerU_mem_layerA v c δ hδ (q := q.1) q.2.1,
         (cuspInvOuter_nrm_Top v c δ q.1 q.2).1,
         (cuspInvOuter_nrm_Top v c δ q.1 q.2).2⟩⟩ :
        {z : ℝ × ℝ // z ∈ layerDomI (cuspAnchor v c)})) :=
    hg.subtype_mk (fun q => ⟨outerU_mem_layerA v c δ hδ (q := q.1) q.2.1,
      (cuspInvOuter_nrm_Top v c δ q.1 q.2).1,
      (cuspInvOuter_nrm_Top v c δ q.1 q.2).2⟩)
  have hYc : Continuous (fun x : E3 => outerY v x) := by unfold outerY kappaCoord; fun_prop
  have hsnd : Continuous (fun q : {q : E4 // q ∈ cuspSourceTop v c δ} => outerY v (xOf q.1)) :=
    hYc.comp (hxOf.comp continuous_subtype_val)
  exact hfst.prodMk hsnd

end Work.Cusp
