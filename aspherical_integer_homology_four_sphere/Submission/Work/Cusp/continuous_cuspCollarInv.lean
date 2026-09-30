import Mathlib
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

/-- **Continuity of the collar height in its two variables.**  For every point `x` of a topological
space at which the ceiling `b x` is non-zero, the collar height `collarHeight (t x) (b x)` is
continuous; both the layer parameter `t = ‖p‖∞` and the ceiling `b = β(x)` vary continuously over
the collar. -/
theorem continuous_collarHeight {X : Type*} [TopologicalSpace X] {t b : X → ℝ}
    (ht : Continuous t) (hb : Continuous b) (hb0 : ∀ x, b x ≠ 0) :
    Continuous (fun x => collarHeight (t x) (b x)) := by
  unfold collarHeight
  refine Real.continuous_exp.comp ?_
  have hlog : Continuous (fun x => Real.log (b x)) := hb.log hb0
  fun_prop

/-- **The inverse of the collar coordinate is continuous.**  The map reassembles a point of `E4`
from its `(u,t,y)`-coordinates by `x = cuspX v u y` and `s = collarHeight t (β x)`; both pieces are
compositions of continuous maps (`cuspX` is linear in `(u,y)`, `β` and `t ↦ collarHeight t b` are
continuous). -/
theorem continuous_cuspCollarInv (v : Fin 5) : Continuous (Work.Cusp.cuspCollarInv v) := by
  have hφ : Continuous (fun p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2 =>
      ((p.1 : ℝ × ℝ).1, p.2)) := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_subtype_val.comp continuous_fst).fst
    · exact continuous_snd
  have hx : Continuous (fun p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2 =>
      cuspX v (p.1 : ℝ × ℝ).1 p.2) := (continuous_cuspX v).comp hφ
  have ht : Continuous (fun p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2 =>
      (p.1 : ℝ × ℝ).2) := (continuous_subtype_val.comp continuous_fst).snd
  have hb : Continuous (fun p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2 =>
      beta (cuspX v (p.1 : ℝ × ℝ).1 p.2)) := beta_continuous.comp hx
  have h2 : Continuous (fun p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2 =>
      collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v (p.1 : ℝ × ℝ).1 p.2))) :=
    continuous_collarHeight ht hb (fun p => ne_of_gt (beta_pos _))
  unfold cuspCollarInv
  exact continuous_mkE4 hx h2

end Work.Cusp
