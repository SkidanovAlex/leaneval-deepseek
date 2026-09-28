import Mathlib
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.OneCell.Compress

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000


/-!
# Vanishing of the rational homology of the preimage of an open `1`-cell

For a Serre fibration `q : E → Z` over `Z = Work.Serre.attachOneCells Y ι f` whose fibres are
rationally acyclic in degrees `0 < k ≤ N` (and have `H₀(-;ℚ) ≅ ℚ`), the preimage of an open
`1`-cell `cellInteriorOne i` (an open interval) has vanishing rational homology in degrees
`0 < k ≤ N`.

The argument is the long exact sequence of the pair `(q⁻¹W, q⁻¹{c})`, where `c` is the centre of
the cell:

* the model interval compresses onto its centre (`compressRel_cellInteriorOne`), and the compression
  engine `isZero_relChains_preimage_of_base_compress` lifts this to the vanishing of the *relative*
  rational homology of the pair `(q⁻¹W, q⁻¹{c})`;
* the subspace `q⁻¹{c} ∩ q⁻¹W` is the fibre `q⁻¹{c}`, which is rationally acyclic;
* exactness of `H_k(q⁻¹{c}) → H_k(q⁻¹W) → H_k(q⁻¹W, q⁻¹{c})` at `H_k(q⁻¹W)` then forces
  `H_k(q⁻¹W;ℚ) = 0` (`pp_isZero_absH_of_isZero_rel`).
-/

namespace Work.Serre.OneCell

theorem isZero_ratH_preimage_cellInteriorOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : ∀ z : Work.Serre.attachOneCells Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (i : ι) (k : ℕ) (hk0 : 0 < k) (hkN : k ≤ N) :
    CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i)) k) := by
  classical
  -- the centre `c` of the cell, and the pair `(q⁻¹W, q⁻¹{c})`
  set c : Work.Serre.attachOneCells Y ι f := Work.Serre.OneCell.oneCellCentreOne Y ι f i
  refine Work.Serre.pp_isZero_absH_of_isZero_rel
    ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i)
    {x : ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i) |
      (x : E) ∈ q ⁻¹' ({c} : Set (Work.Serre.attachOneCells Y ι f))} k ?hA ?hrel
  · -- the fibre over the centre is rationally acyclic
    have hset : {x : ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i) |
        (x : E) ∈ q ⁻¹' ({c} : Set (Work.Serre.attachOneCells Y ι f))} =
        {x : ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i) | q (x : E) = c} := by
      ext x
      simp
    rw [hset]
    have hc : c ∈ Work.Serre.OneCell.cellInteriorOne Y ι f i := by
      rw [show c = Work.Serre.OneCell.oneCellCentreOne Y ι f i from rfl]
      exact Work.Serre.OneCell.oneCellCentreOne_mem_cellInteriorOne f i
    exact Work.Serre.OneCell.isZero_ratH_of_homeo
      (Work.Serre.OneCell.homeoSubFibre q hc) k
      ((hacyc c).1 k hk0 hkN)
  · -- the relative rational homology of the pair vanishes by the compression engine
    have hrelZ : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i))
          {x : ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i) |
            (x : E) ∈ q ⁻¹' ({c} : Set (Work.Serre.attachOneCells Y ι f))}).homology k) := by
      refine Work.Serre.isZero_relChains_preimage_of_base_compress q hq ({c} : Set _)
        (Work.Serre.OneCell.cellInteriorOne Y ι f i) ?hW ?hb k
      · -- the centre lies in the open cell
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Work.Serre.OneCell.oneCellCentreOne_mem_cellInteriorOne f i
      · -- the model pair `(cell interior, centre)` is compressible
        intro d
        have hset : {x : ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i) |
            (x : Work.Serre.attachOneCells Y ι f) ∈
              ({c} : Set (Work.Serre.attachOneCells Y ι f))} =
            {x : ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i) |
              (x : Work.Serre.attachOneCells Y ι f) =
                Work.Serre.OneCell.oneCellCentreOne Y ι f i} := by
          ext x
          simp [show c = Work.Serre.OneCell.oneCellCentreOne Y ι f i from rfl]
        rw [hset]
        exact Work.Serre.OneCell.compressRel_cellInteriorOne (Y := Y) (ι := ι) (f := f) i d
    exact Work.Serre.OneCell.isZero_ppRelH_of_isZero_relChains _ _ k hrelZ

end Work.Serre.OneCell
