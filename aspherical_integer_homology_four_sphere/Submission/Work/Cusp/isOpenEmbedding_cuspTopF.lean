import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.Cusp.continuous_cuspTopInv
import Submission.Work.Cusp.continuous_cuspTopF
import Submission.Work.Cusp.mem_range_cuspTopF
import Submission.Work.Cusp.cuspTopInv_apply_cuspTopF
import Submission.Work.Cusp.isOpenEmbedding_cuspCollarF

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The unslabbed collar coordinate is an open embedding.**  The proof is the same as for the
slabbed family `isOpenEmbedding_cuspCollarF`:

* `cuspTopInv v (cuspAnchor v c)` is a continuous left inverse of `cuspTopF v c δ hδ` on the
  collar source (`cuspTopInv_apply_cuspTopF`), so composing with it turns the embedding
  `Subtype.val` into `cuspTopInv v (cuspAnchor v c) ∘ cuspTopF v c δ hδ`; since both maps are
  continuous, `Topology.IsEmbedding.of_comp` gives that `cuspTopF v c δ hδ` is an embedding.

* The range of `cuspTopF v c δ hδ` is the preimage of the open box `cuspBoxTop v c δ` under the
  continuous reassembly map `cuspTopInv v (cuspAnchor v c)` (`mem_range_cuspTopF`,
  `isOpen_cuspBoxTop`), hence open. -/
theorem isOpenEmbedding_cuspTopF (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Topology.IsOpenEmbedding (cuspTopF v c δ hδ) := by
  have hG : Continuous (cuspTopInv v (cuspAnchor v c)) := continuous_cuspTopInv v _
  have hcont : Continuous (cuspTopF v c δ hδ) := continuous_cuspTopF v c δ hδ
  have hcomp : Topology.IsEmbedding (cuspTopInv v (cuspAnchor v c) ∘ cuspTopF v c δ hδ) := by
    rw [show cuspTopInv v (cuspAnchor v c) ∘ cuspTopF v c δ hδ = Subtype.val from
      funext fun q => cuspTopInv_apply_cuspTopF v c δ hδ q]
    exact Topology.IsEmbedding.subtypeVal
  have hemb : Topology.IsEmbedding (cuspTopF v c δ hδ) :=
    Topology.IsEmbedding.of_comp hcont hG hcomp
  have hopen : IsOpen (Set.range (cuspTopF v c δ hδ)) := by
    rw [show Set.range (cuspTopF v c δ hδ) =
        (cuspTopInv v (cuspAnchor v c)) ⁻¹' cuspBoxTop v c δ from
      Set.ext fun p => mem_range_cuspTopF v c δ hδ p]
    exact (isOpen_cuspBoxTop v c δ).preimage hG
  exact ⟨hemb, hopen⟩

end Work.Cusp
