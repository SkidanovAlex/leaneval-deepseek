/-
# The cocycle identity of the cell atlas of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: `Enode` of a node lies in `KsubAtlas` of its
face (`Enode_mem_KsubAtlas`, from the witness `moWit`), the finite check of the cocycle identity on the
subset sums (`cocycle_filter`), and the resulting identity `Enode (γ · x) = Enode x + γ` for all
`γ ∈ KsubAtlas x.2` (`Enode_cocycle`).
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasKsub
import Submission.Work.MbarHomology.Mbar.AtlasCellData
import Submission.Work.MbarHomology.Mbar.AtlasDimData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells
open scoped BigOperators

noncomputable section


open Work.Subdivision Work.ConvexCells
open scoped BigOperators

theorem rootNode_cell (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    moCell (moRootC (moCid n e)) (moRoot (moCid n e)) = moCid n e := by decide +revert

theorem sigVec_rootNode (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    sigVec (moRootC (moCid n e)) (moRoot (moCid n e)) = 0 := by
  have h := sigVec_toRoot (moRootC (moCid n e)) (moRoot (moCid n e))
  simp only [toRoot] at h
  rw [rootNode_cell n e] at h
  exact h

theorem toRoot_rootNode (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    toRoot (moRootC (moCid n e)) (moRoot (moCid n e))
      = (moRootC (moCid n e), moRoot (moCid n e)) := by
  have h := toRoot_fixed (moRootC (moCid n e)) (moRoot (moCid n e))
  simp only [toRoot] at h
  rw [rootNode_cell n e] at h
  exact h

theorem Enode_mem_KsubAtlas (c : ZMod 2) (F : Fin 865) : Enode c F ∈ KsubAtlas F := by
  rw [mem_KsubAtlas_iff]
  refine ⟨(moWit c F).toFinset, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro S hS
    rw [mem_tightSidesIdx]
    exact mem_qTight_of_mem_moWit c F S hS
  · simpa only [sideTypeSum] using Enode_wit c F


/-- The cocycle identity, as a computable check on all subset sums: the set of subsets for which
the identity fails is empty. -/
def cocycleOk (c : ZMod 2) (F : Fin 865) : Bool :=
  decide (((tightSidesIdx F).powerset.filter
    (fun A => ¬ (Enode (nodeAct (sideTypeSum A) (c, F)).1 (nodeAct (sideTypeSum A) (c, F)).2
                 = Enode c F + sideTypeSum A))).card = 0)

theorem cocycleOk_c0 : ∀ c : ZMod 2, ∀ F : Fin 865, 0 ≤ F.val → F.val < 55 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c1 : ∀ c : ZMod 2, ∀ F : Fin 865, 55 ≤ F.val → F.val < 110 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c2 : ∀ c : ZMod 2, ∀ F : Fin 865, 110 ≤ F.val → F.val < 165 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c3 : ∀ c : ZMod 2, ∀ F : Fin 865, 165 ≤ F.val → F.val < 220 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c4 : ∀ c : ZMod 2, ∀ F : Fin 865, 220 ≤ F.val → F.val < 275 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c5 : ∀ c : ZMod 2, ∀ F : Fin 865, 275 ≤ F.val → F.val < 330 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c6 : ∀ c : ZMod 2, ∀ F : Fin 865, 330 ≤ F.val → F.val < 385 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c7 : ∀ c : ZMod 2, ∀ F : Fin 865, 385 ≤ F.val → F.val < 440 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c8 : ∀ c : ZMod 2, ∀ F : Fin 865, 440 ≤ F.val → F.val < 495 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c9 : ∀ c : ZMod 2, ∀ F : Fin 865, 495 ≤ F.val → F.val < 550 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c10 : ∀ c : ZMod 2, ∀ F : Fin 865, 550 ≤ F.val → F.val < 605 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c11 : ∀ c : ZMod 2, ∀ F : Fin 865, 605 ≤ F.val → F.val < 660 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c12 : ∀ c : ZMod 2, ∀ F : Fin 865, 660 ≤ F.val → F.val < 715 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c13 : ∀ c : ZMod 2, ∀ F : Fin 865, 715 ≤ F.val → F.val < 770 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c14 : ∀ c : ZMod 2, ∀ F : Fin 865, 770 ≤ F.val → F.val < 825 → cocycleOk c F = true := by
  decide +kernel
theorem cocycleOk_c15 : ∀ c : ZMod 2, ∀ F : Fin 865, 825 ≤ F.val → cocycleOk c F = true := by
  decide +kernel
/-- `cocycleOk` holds everywhere (checked in blocks of faces). -/
theorem cocycleOk_all (c : ZMod 2) (F : Fin 865) : cocycleOk c F = true := by
  by_cases h0 : F.val < 55
  · exact cocycleOk_c0 c F (by omega) h0
  by_cases h1 : F.val < 110
  · exact cocycleOk_c1 c F (by omega) h1
  by_cases h2 : F.val < 165
  · exact cocycleOk_c2 c F (by omega) h2
  by_cases h3 : F.val < 220
  · exact cocycleOk_c3 c F (by omega) h3
  by_cases h4 : F.val < 275
  · exact cocycleOk_c4 c F (by omega) h4
  by_cases h5 : F.val < 330
  · exact cocycleOk_c5 c F (by omega) h5
  by_cases h6 : F.val < 385
  · exact cocycleOk_c6 c F (by omega) h6
  by_cases h7 : F.val < 440
  · exact cocycleOk_c7 c F (by omega) h7
  by_cases h8 : F.val < 495
  · exact cocycleOk_c8 c F (by omega) h8
  by_cases h9 : F.val < 550
  · exact cocycleOk_c9 c F (by omega) h9
  by_cases h10 : F.val < 605
  · exact cocycleOk_c10 c F (by omega) h10
  by_cases h11 : F.val < 660
  · exact cocycleOk_c11 c F (by omega) h11
  by_cases h12 : F.val < 715
  · exact cocycleOk_c12 c F (by omega) h12
  by_cases h13 : F.val < 770
  · exact cocycleOk_c13 c F (by omega) h13
  by_cases h14 : F.val < 825
  · exact cocycleOk_c14 c F (by omega) h14
  exact cocycleOk_c15 c F (by omega)

/-- **The cocycle identity, checked on subset sums.** -/
theorem cocycle_filter (c : ZMod 2) (F : Fin 865) :
    ((tightSidesIdx F).powerset.filter
      (fun A => Enode (nodeAct (sideTypeSum A) (c, F)).1 (nodeAct (sideTypeSum A) (c, F)).2
                 ≠ Enode c F + sideTypeSum A)) = ∅ := by
  have h : cocycleOk c F = true := cocycleOk_all c F
  have h2 : ((tightSidesIdx F).powerset.filter
      (fun A => ¬ (Enode (nodeAct (sideTypeSum A) (c, F)).1 (nodeAct (sideTypeSum A) (c, F)).2
                 = Enode c F + sideTypeSum A))).card = 0 := by
    simpa only [cocycleOk] using of_decide_eq_true h
  rw [Finset.card_eq_zero] at h2
  simpa only [ne_eq] using h2

theorem Enode_cocycle {γ : Work.FoldInst.Gg} {F : Fin 865} (hγ : γ ∈ KsubAtlas F) (c : ZMod 2) :
    Enode (nodeAct γ (c, F)).1 (nodeAct γ (c, F)).2 = Enode c F + γ := by
  obtain ⟨A, hA, rfl⟩ := (mem_KsubAtlas_iff F γ).mp hγ
  by_contra hne
  have hmem : A ∈ (tightSidesIdx F).powerset.filter
      (fun A => Enode (nodeAct (sideTypeSum A) (c, F)).1 (nodeAct (sideTypeSum A) (c, F)).2
                 ≠ Enode c F + sideTypeSum A) := Finset.mem_filter.mpr ⟨hA, hne⟩
  rw [cocycle_filter] at hmem
  exact absurd hmem (by simp)

end

end Work.MbarHomology.Mbar
