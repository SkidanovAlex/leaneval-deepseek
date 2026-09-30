import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.mem_range_cuspCollarF
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.collarHeight_inv
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The layer parameter recovered from the point `(cuspX v u y, collarHeight t (β (cuspX v u y)))`
is `t`.**  This is the round trip `collarHeight`/`cuspInvOuter` at the ceiling `β x`: by
`collarHeight_inv` the logarithmic formula which defines the recovered layer parameter of
`cuspInvOuter` returns `t`, and since `t > 0` its sup norm `‖t • bndOfU _‖∞ = |t|` is `t` itself.

No hypothesis on the size of `t` other than positivity is needed: the formula inverts
`collarHeight · (β x)` at the single value `t`, and `t > 0` makes the sup norm of `t • bndOfU _`
equal to `t`. -/
theorem nrm_cuspInvOuter_mkE4 (v : Fin 5) (x : E3) (t : ℝ) (ht : 0 < t) :
    nrm (cuspInvOuter v (mkE4 x (collarHeight t (beta x)))).1 = t := by
  have hbpos : 0 < beta x := beta_pos x
  have hbne : beta x ≠ sJ := ne_of_lt (lt_of_le_of_lt (beta_le_max x) betaMax_lt_sJ)
  -- the logarithmic formula defining the recovered layer parameter returns `t`
  have hTinv : 1 + (Real.log (collarHeight t (beta x)) - Real.log (beta x)) /
      (2 * (Real.log (beta x) - Real.log sJ)) = t :=
    (collarHeight_inv t (beta x) (collarHeight t (beta x)) hbpos hbne rfl).symm
  -- unfold `cuspInvOuter` at this point
  have hpe : (cuspInvOuter v (mkE4 x (collarHeight t (beta x)))).1
      = (1 + (Real.log ((mkE4 x (collarHeight t (beta x))) 3)
            - Real.log (beta (xOf (mkE4 x (collarHeight t (beta x)))))) /
          (2 * (Real.log (beta (xOf (mkE4 x (collarHeight t (beta x))))) - Real.log sJ)))
          • bndOfU (outerU v (xOf (mkE4 x (collarHeight t (beta x))))) := rfl
  rw [hpe, mkE4_apply_three, xOf_mkE4, nrm_smul, nrm_bndOfU, mul_one, hTinv, abs_of_pos ht]

/-- **`cuspTopF` is a left inverse of `cuspTopInv`.**  The collar coordinate `cuspTopF v c δ hδ`
sends a point `q` of the collar source to `(u, t, y) = (outerU v (xOf q), ‖(cuspInvOuter v q).1‖∞,
outerY v (xOf q))`; reassembling the point of `E4` from `(u,t,y)` by
`cuspTopInv v a ((u,t),y) = (cuspX v u y, collarHeight t (β (cuspX v u y)))` and applying `cuspTopF`
again returns `(u,t,y)`:

* the perimeter coordinate comes back by `outerU_cuspX`;
* the phase comes back by `outerY_cuspX`;
* the layer parameter comes back by `nrm_cuspInvOuter_mkE4`.

The hypothesis `p ∈ layerDomI (cuspAnchor v c)` (built into the type of `p`) supplies exactly
`t > 1/4 > 0`; the membership `hp` of the reassembled point in the collar source is only what makes
`cuspTopF` applicable, and the identity itself holds for every `p` of the target. -/
theorem cuspTopF_apply_cuspTopInv (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (p : {z : ℝ × ℝ // z ∈ layerDomI (cuspAnchor v c)} × E2)
    (hp : cuspTopInv v (cuspAnchor v c) p ∈ cuspSourceTop v c δ) :
    cuspTopF v c δ hδ ⟨cuspTopInv v (cuspAnchor v c) p, hp⟩ = p := by
  -- the horizontal part `cuspX v u y` of the reassembled point recovers `(u,y)`
  have hU : outerU v (xOf (cuspTopInv v (cuspAnchor v c) p)) = (p.1 : ℝ × ℝ).1 := by
    rw [cuspTopInv, xOf_mkE4, outerU_cuspX]
  have hY : outerY v (xOf (cuspTopInv v (cuspAnchor v c) p)) = p.2 := by
    rw [cuspTopInv, xOf_mkE4, outerY_cuspX]
  -- `t = ‖p.1‖∞ > 1/4 > 0` by the layer domain of `p`
  have htpos : 0 < (p.1 : ℝ × ℝ).2 :=
    lt_trans (by norm_num [layerLo]) p.1.2.2.1
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    rw [cuspTopF_fst]
    exact Prod.ext hU
      (nrm_cuspInvOuter_mkE4 v (cuspX v (p.1 : ℝ × ℝ).1 p.2) (p.1 : ℝ × ℝ).2 htpos)
  · rw [cuspTopF_snd]
    exact hY

end Work.Cusp
