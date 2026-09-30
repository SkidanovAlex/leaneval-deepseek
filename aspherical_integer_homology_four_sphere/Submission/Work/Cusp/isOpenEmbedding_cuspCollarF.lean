/-
# The collar coordinate `cuspCollarF` is an open embedding

`cuspCollarF v c δ` (`Work.Cusp.CuspChartAux`) writes a point `q = (x,s)` of the collar source
`cuspCollarSource v c δ` of the chart box in its `(u,t,y)`-coordinates: the perimeter coordinate
`u = outerU v x`, the layer parameter `t = ‖(cuspInvOuter v q).1‖∞` recovered from the height by
inverting the collar height, and the phase `y = outerY v x`.

The proof that this is an open embedding has three parts.

* **The inverse.**  `cuspCollarInv v` (`Work.Cusp.CuspCollarAux`) reassembles the point of `E4`
from `(u,t,y)` by `x = cuspX v u y` and `s = collarHeight t (β x)`.  It is continuous
(`continuous_cuspCollarInv`) and it is a left inverse of `cuspCollarF` on the collar source
(`cuspCollarInv_apply_cuspCollarF`), i.e. `cuspCollarInv v ∘ cuspCollarF v c δ = Subtype.val`.
Since `Subtype.val` is an embedding and the two maps are continuous, `Topology.IsEmbedding.of_comp`
gives that `cuspCollarF v c δ` is an embedding.

* **The range.**  `p` lies in the range of `cuspCollarF v c δ` exactly when its `(u,y)`-coordinates
lie in the box `cuspCollarBox v c δ` (`mem_range_cuspCollarF`), the open condition
`∀ i, |(cuspX v u y) i − c i| < δ` (`isOpen_cuspCollarBox`); the layer parameter `t` is
automatically in `(1/2,1]` by the type of the target.

* Hence the range — the preimage of the open box `cuspCollarBox v c δ` under the continuous
`(u,y)`-coordinate projection (`continuous_cuspCollarCoords`) — is open, and an embedding with open
range is an open embedding.

The ingredients of the second and third bullet are the files
`Submission/Work/Cusp/{continuous_cuspCollarInv, continuous_cuspCollarF,
cuspCollarInv_apply_cuspCollarF, mem_range_cuspCollarF}.lean`.
-/
import Mathlib
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.continuous_cuspCollarF
import Submission.Work.Cusp.cuspCollarInv_apply_cuspCollarF
import Submission.Work.Cusp.mem_range_cuspCollarF

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

theorem isOpenEmbedding_cuspCollarF (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) : Topology.IsOpenEmbedding (Work.Cusp.cuspCollarF v c δ) := by
  -- `cuspCollarInv v` is a continuous left inverse of `cuspCollarF v c δ`
  have hG : Continuous (cuspCollarInv v) := continuous_cuspCollarInv v
  have hcont : Continuous (cuspCollarF v c δ) := continuous_cuspCollarF v c δ
  have hcomp : Topology.IsEmbedding (cuspCollarInv v ∘ cuspCollarF v c δ) := by
    rw [show cuspCollarInv v ∘ cuspCollarF v c δ = Subtype.val from
      funext fun q => cuspCollarInv_apply_cuspCollarF v c δ q]
    exact Topology.IsEmbedding.subtypeVal
  have hemb : Topology.IsEmbedding (cuspCollarF v c δ) :=
    Topology.IsEmbedding.of_comp hcont hG hcomp
  -- the range is the preimage of the open box `cuspCollarBox v c δ` under the `(u,y)`-coordinates
  have hopen : IsOpen (Set.range (cuspCollarF v c δ)) := by
    rw [show Set.range (cuspCollarF v c δ) = cuspCollarCoords ⁻¹' cuspCollarBox v c δ from
      Set.ext fun p => mem_range_cuspCollarF v c δ p]
    exact (isOpen_cuspCollarBox v c δ).preimage continuous_cuspCollarCoords
  exact ⟨hemb, hopen⟩

end Work.Cusp
