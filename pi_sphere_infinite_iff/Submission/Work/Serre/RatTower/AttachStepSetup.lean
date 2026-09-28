import Mathlib
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.RatTower.pullbackFstRangeHomeo
import Submission.Work.Serre.RatTower.fiveLemmaTau2
import Submission.Work.Serre.RatTower.Attach
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.PerCell.isIso_csrRelMapOf_homeo
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

/-!
# The `ℚ`-cell step of the tower comparison: formal setup

This module contains the (coefficient-`ℚ`) formal part of the cell-attachment step of the tower
comparison `Work.Serre.RatTower.attachStepQ`: the naturality of `cokernel.π` with respect to the
three comparison maps of the step, and the two short exact triple sequences together with the
morphism between them.

Nothing here is analytic: the geometric input is the hypothesis `Work.Serre.RatCellStepSharp`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.RatTower

noncomputable section

/-! ## Naturality of `cokernel.π` for the comparison maps -/

/-- **The naturality of `cokernel.π` with respect to the cell step map.** -/
theorem cokernel_π_cellStepMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of E)
        {e : E | q e ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)})
      ≫ Work.Serre.cellStepMap n ι f q
      = Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
          (TopCat.ofHom q)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ
            (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
            (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) := by
  unfold Work.Serre.cellStepMap
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **The naturality of `cokernel.π` with respect to `stagePairMapRat`.** -/
theorem cokernel_π_stagePairMapRat {B E Γ : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ
        (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
      ≫ Work.Serre.stagePairMapRat g p γ₀
      = Work.Cohomology.chainMap ℚ (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of Γ)
          (TopCat.ofHom (Work.StemsB.pullbackFst g p))
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ) ({γ₀} : Set Γ)) := by
  unfold Work.Serre.stagePairMapRat Work.Serre.relChainsRPairMap
  exact Work.Serre.cokernel_π_csrRelMapOf

/-- The first map of `tripleShortR`, exposed. -/
theorem tripleShortR_f_eq (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShortR X A B hAB).f
      = cokernel.map
          (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
          (Work.StemsB.relChainsRIncl ℚ X A)
          (Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A)
            (Work.Cohomology.inclInterA X B A))
          (Work.StemsB.relChainsRIncl ℚ X B)
          (by
            show Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥B)
                  (Work.Cohomology.subtypeIncl (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
                  ≫ Work.Cohomology.chainMap ℚ (TopCat.of ↥B) X (Work.Cohomology.subtypeIncl X B)
                = Work.Cohomology.chainMap ℚ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A)
                    (Work.Cohomology.inclInterA X B A)
                  ≫ Work.Cohomology.chainMap ℚ (TopCat.of ↥A) X (Work.Cohomology.subtypeIncl X A)
            rw [← chainMapQ_comp, ← chainMapQ_comp, subtypeIncl_interInclInterA X A B hAB]) := rfl

/-- The second map of `tripleShortR`, exposed. -/
theorem tripleShortR_g_eq (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShortR X A B hAB).g
      = cokernel.desc (Work.StemsB.relChainsRIncl ℚ X A)
          (cokernel.π (Work.StemsB.relChainsRIncl ℚ X B))
          (by
            show Work.Cohomology.chainMap ℚ (TopCat.of ↥A) X (Work.Cohomology.subtypeIncl X A)
                  ≫ cokernel.π (Work.Cohomology.chainMap ℚ (TopCat.of ↥B) X
                      (Work.Cohomology.subtypeIncl X B)) = 0
            rw [← inclTop_subtypeIncl X A B hAB, chainMapQ_comp, Category.assoc,
              cokernel.condition, comp_zero]) := rfl

/-- **The naturality of `cokernel.π` with respect to the first map of the triple sequence.** -/
theorem cokernel_π_tripleShortR_f (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
      ≫ (tripleShortR X A B hAB).f
      = Work.StemsB.relChainsRIncl ℚ X B
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) := by
  rw [tripleShortR_f_eq]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **The naturality of `cokernel.π` with respect to the second map of the triple sequence.** -/
theorem cokernel_π_tripleShortR_g (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) ≫ (tripleShortR X A B hAB).g
      = cokernel.π (Work.StemsB.relChainsRIncl ℚ X B) := by
  rw [tripleShortR_g_eq]
  exact cokernel.π_desc _ _ _

end

end Work.Serre.RatTower
