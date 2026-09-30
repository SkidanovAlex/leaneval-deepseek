import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.CuspCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The inverse of the unslabbed collar coordinate is continuous.**  The map reassembles a point
of `E4` from its `(u,t,y)`-coordinates by `x = cuspX v u y` and `s = collarHeight t (β x)`; both
pieces are compositions of continuous maps (`cuspX` is linear in `(u,y)`, `β` is continuous and
`t ↦ collarHeight t b` is continuous), exactly as for the slabbed family
`continuous_cuspCollarInv`. -/
theorem continuous_cuspTopInv (v : Fin 5) (a : ℝ) : Continuous (cuspTopInv v a) := by
  have hφ : Continuous (fun p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2 =>
      ((p.1 : ℝ × ℝ).1, p.2)) := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_subtype_val.comp continuous_fst).fst
    · exact continuous_snd
  have hx : Continuous (fun p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2 =>
      cuspX v (p.1 : ℝ × ℝ).1 p.2) := (continuous_cuspX v).comp hφ
  have ht : Continuous (fun p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2 =>
      (p.1 : ℝ × ℝ).2) := (continuous_subtype_val.comp continuous_fst).snd
  have hb : Continuous (fun p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2 =>
      beta (cuspX v (p.1 : ℝ × ℝ).1 p.2)) := beta_continuous.comp hx
  have h2 : Continuous (fun p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2 =>
      collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v (p.1 : ℝ × ℝ).1 p.2))) :=
    continuous_collarHeight ht hb (fun p => ne_of_gt (beta_pos _))
  unfold cuspTopInv
  exact continuous_mkE4 hx h2

end Work.Cusp
