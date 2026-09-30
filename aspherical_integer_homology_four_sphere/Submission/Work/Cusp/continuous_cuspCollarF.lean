/-
# Continuity of the collar coordinate `cuspCollarF`

`cuspCollarF v c δ` (`Work.Cusp.CuspChartAux`) sends a point `q` of the collar source
`cuspCollarSource v c δ ⊆ E4` to its `(u,t,y)`-coordinates

  `(u, t, y) = (outerU v (xOf q), ‖(cuspInvOuter v q).1‖∞, outerY v (xOf q))`,

the first two coordinates bundled as an element of the subtype `{z : ℝ × ℝ // z ∈ collarLayerDom}`
of the layer parameter domain `(0,1) × (1/2,1]`.

Each ingredient is continuous on the source:

* `q ↦ outerU v (xOf q)` and `q ↦ outerY v (xOf q)`: `outerU v`, `outerY v` are fixed linear maps
  of the horizontal part `xOf q`, and `xOf` is continuous (`outerU_continuous`,
  `Work.Cusp.continuous_outerY`);
* `q ↦ ‖(cuspInvOuter v q).1‖∞`: `cuspInvOuter v` is continuous on the half space `{q | 0 < q 3}`
  (`cuspInvOuter_continuousOn`), and the source lies in that half space because it lies in the cusp
  box `cuspBox v c δ`, whose height condition is `s₁ < q 3` with `s₁ = 11/10 > 0`; composing with
  the continuous `nrm` (`nrm_continuous`) gives the claim.

Continuity into a subtype of `ℝ × ℝ` is continuity of the underlying pair
(`Continuous.subtype_mk`), and continuity into the product `_ × E2` is continuity of the two
components (`Continuous.prodMk`).
-/
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

theorem continuous_cuspCollarF (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) :
    Continuous (Work.Cusp.cuspCollarF v c δ) := by
  -- `xOf` is the continuous horizontal-part map `E4 → E3`.
  have hxOf : Continuous (fun q : E4 => xOf q) := by
    unfold xOf
    fun_prop
  -- The perimeter coordinate `outerU v (xOf q)`.
  have hu : Continuous (fun q : {q : E4 // q ∈ cuspCollarSource v c δ} => outerU v (xOf q.1)) :=
    (outerU_continuous v).comp (hxOf.comp continuous_subtype_val)
  -- The collar source lies in the half space `{q | 0 < q 3}` where the inverse chart is continuous.
  have hS : ∀ q : {q : E4 // q ∈ cuspCollarSource v c δ}, 0 < q.1 3 := by
    intro q
    have h := q.2.1.1.2.1
    have hs1pos : (0 : ℝ) < s1 := by norm_num [s1]
    linarith
  -- The recovered inverse chart and its sup norm `t = ‖(cuspInvOuter v q).1‖∞`.
  have hinv : Continuous (fun q : {q : E4 // q ∈ cuspCollarSource v c δ} => cuspInvOuter v q.1) :=
    (cuspInvOuter_continuousOn v).comp_continuous continuous_subtype_val hS
  have hnrm : Continuous
      (fun q : {q : E4 // q ∈ cuspCollarSource v c δ} => nrm (cuspInvOuter v q.1).1) :=
    nrm_continuous.comp hinv.fst
  -- The phase coordinate `outerY v (xOf q)`.
  have hy : Continuous (fun q : {q : E4 // q ∈ cuspCollarSource v c δ} => outerY v (xOf q.1)) :=
    (continuous_outerY v).comp (hxOf.comp continuous_subtype_val)
  -- The pair `(u, t)` of the first two coordinates.
  have hfst : Continuous (fun q : {q : E4 // q ∈ cuspCollarSource v c δ} =>
      (outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1)) := hu.prodMk hnrm
  -- Bundle `(u, t)` into the subtype `collarLayerDom`; the membership is the one recorded by the
  -- definition of `cuspCollarF`.
  have hsub : Continuous (fun q : {q : E4 // q ∈ cuspCollarSource v c δ} =>
      (⟨(outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1),
        ⟨q.2.2, q.2.1.1.2.2.2.2,
          (cuspInvOuter_mem_cuspStratum v c δ q.1 q.2.1).1,
          (cuspInvOuter_mem_cuspStratum v c δ q.1 q.2.1).2⟩⟩ :
        {z : ℝ × ℝ // z ∈ collarLayerDom})) :=
    Continuous.subtype_mk hfst _
  exact hsub.prodMk hy

end Work.Cusp
