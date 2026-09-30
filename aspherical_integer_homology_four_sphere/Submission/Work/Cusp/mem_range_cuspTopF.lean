import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.cuspTopInv_apply_cuspTopF
import Submission.Work.Cusp.cuspTopF_apply_cuspTopInv
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.collarHeight_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The range of the unslabbed collar coordinate is the box of `(u,y)`-coordinates.**  A point
`p = ((u,t), y)` of the layer target (with `(u,t) ∈ (outerU v c − 1/2, outerU v c + 1/2) × (1/4,1]`)
lies in the range of `cuspTopF v c δ hδ` exactly when the reassembled point
`cuspTopInv v (cuspAnchor v c) p = (cuspX v u y, collarHeight t (β (cuspX v u y)))` lies in the box
of side `2δ` around `c`.

Forward: for `q` in the collar source, `cuspTopInv v (cuspAnchor v c) (cuspTopF v c δ hδ q) = q.1`
(`cuspTopInv_apply_cuspTopF`), and `q.1` lies in the box because `q ∈ cuspSourceTop v c δ`.

Converse: if the reassembly `q = cuspTopInv v (cuspAnchor v c) p` lies in the box, then it lies on or
above the ceiling — `β x ≤ collarHeight t (β x)` for `t ≤ 1`, which is the antitonicity of
`collarHeight · (β x)` at `t ≤ 1` together with `collarHeight 1 b = b` — so `q` is a point of the
collar source, and applying `cuspTopF` to it returns `p` by `cuspTopF_apply_cuspTopInv` (`p`'s layer
parameter is `> 1/4 > 0`, and the two coordinates `outerU v (cuspX v u y) = u`,
`outerY v (cuspX v u y) = y` come back, while the recovered layer parameter is `t` itself). -/
theorem mem_range_cuspTopF (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (p : {z : ℝ × ℝ // z ∈ layerDomI (cuspAnchor v c)} × E2) :
    p ∈ Set.range (cuspTopF v c δ hδ) ↔
      cuspTopInv v (cuspAnchor v c) p ∈ cuspBoxTop v c δ := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [cuspTopInv_apply_cuspTopF v c δ hδ q]
    exact q.2.1
  · intro hbox
    -- the ceiling of the reassembled point: `β x ≤ collarHeight t (β x)` for `t ≤ 1`
    have htpos : 0 < (p.1 : ℝ × ℝ).2 := lt_trans (by norm_num [layerLo]) p.1.2.2.1
    have ht1 : (p.1 : ℝ × ℝ).2 ≤ 1 := p.1.2.2.2
    have hbx : 0 < beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2) := beta_pos _
    have hbJ : beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2) < sJ :=
      lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
    have hceil : beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2) ≤
        collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2)) := by
      rcases lt_or_eq_of_le ht1 with hlt | heq
      · have h : collarHeight (1 : ℝ) (beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2)) <
            collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2)) :=
          (collarHeight_strictAntiOn _ hbx hbJ)
            (Set.mem_univ (p.1 : ℝ × ℝ).2) (Set.mem_univ (1 : ℝ)) hlt
        rw [collarHeight_one _ hbx] at h
        exact le_of_lt h
      · rw [heq, collarHeight_one _ hbx]
    -- the two coordinates of the reassembled point
    have hxof : xOf (cuspTopInv v (cuspAnchor v c) p) = cuspX v ((p.1 : ℝ × ℝ).1) p.2 := by
      rw [cuspTopInv, xOf_mkE4]
    have hthree : (cuspTopInv v (cuspAnchor v c) p) 3
        = collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v ((p.1 : ℝ × ℝ).1) p.2)) := by
      rw [cuspTopInv, mkE4_apply_three]
    -- the reassembled point is a point of the collar source
    have hsrc : cuspTopInv v (cuspAnchor v c) p ∈ cuspSourceTop v c δ :=
      ⟨hbox, by rw [hxof, hthree]; exact hceil⟩
    exact ⟨⟨_, hsrc⟩, cuspTopF_apply_cuspTopInv v c δ hδ p hsrc⟩

end Work.Cusp
