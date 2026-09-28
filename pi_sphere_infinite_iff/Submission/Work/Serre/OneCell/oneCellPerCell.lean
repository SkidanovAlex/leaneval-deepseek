import Mathlib
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.Serre.OneCell.RatMap
import Submission.Work.Serre.OneCell.LocalInputs
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.OneCell.Halves
import Submission.Work.Serre.OneCell.HalfVanishing
import Submission.Work.Serre.OneCell.Assembly
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.E2dEngine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre.OneCell

theorem oneCellPerCell (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : ∀ z : Work.Serre.attachOneCells Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (m : ℕ) (hm : m ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.OneCell.pairMapQ
        {x : ↥(q ⁻¹' (Work.Serre.OneCell.cellInnerUnionOne Y ι f)) |
          (x : E) ∈ q ⁻¹' (Work.Serre.OneCell.cellInnerUnionOne Y ι f \
            Work.Serre.OneCell.oneCellCentresOne Y ι f)}
        {x : ↥(Work.Serre.OneCell.cellInnerUnionOne Y ι f) |
          (x : Work.Serre.attachOneCells Y ι f) ∈
            (Work.Serre.OneCell.cellInnerUnionOne Y ι f \
              Work.Serre.OneCell.oneCellCentresOne Y ι f)}
        ⟨fun x => ⟨q x.1, x.2⟩, by fun_prop⟩
        (by intro x hx; exact hx)) m) := by
  haveI hfib : Work.Serre.OneCell.FibreAcyclic (Y := Y) (ι := ι) (f := f) E q N := hacyc
  refine Work.Serre.OneCell.isIso_pairMapQ_of
    {x : ↥(q ⁻¹' (Work.Serre.OneCell.cellInnerUnionOne Y ι f)) |
      (x : E) ∈ q ⁻¹' (Work.Serre.OneCell.cellInnerUnionOne Y ι f \
        Work.Serre.OneCell.oneCellCentresOne Y ι f)}
    {x : ↥(Work.Serre.OneCell.cellInnerUnionOne Y ι f) |
      (x : Work.Serre.attachOneCells Y ι f) ∈
        (Work.Serre.OneCell.cellInnerUnionOne Y ι f \
          Work.Serre.OneCell.oneCellCentresOne Y ι f)}
    ⟨fun x => ⟨q x.1, x.2⟩, by fun_prop⟩ (by intro x hx; exact hx) m ?_ ?_
  · intro k hk
    exact Work.Serre.OneCell.isIso_ratHomologyMap_restrictTo_cellInnerUnionOne q hq N hfib k (le_trans hk hm)
  · intro k hk
    exact Work.Serre.OneCell.isIso_ratHomologyMap_subPair q hq N hfib k (le_trans hk hm)

end Work.Serre.OneCell
