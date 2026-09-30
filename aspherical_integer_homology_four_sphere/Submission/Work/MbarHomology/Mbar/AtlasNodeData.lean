/-
# The finite node data of the cell atlas of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the finite checks on the generated tables
`Submission/Work/MbarHomology/Data/MbarOrbits.lean` that involve running `decide` over the `1730`
nodes `(c, F)`.  They are isolated in this file because each `decide` proof term is large.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasData

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

/-- **The finite data of a node**: the element `Enode` moves it to the root of its cell, and the
root node is fixed by `toRoot`. -/
theorem node_facts_c0 : ∀ (c : ZMod 2) (F : Fin 865), 0 ≤ F.val → F.val < 110 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c1 : ∀ (c : ZMod 2) (F : Fin 865), 110 ≤ F.val → F.val < 220 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c2 : ∀ (c : ZMod 2) (F : Fin 865), 220 ≤ F.val → F.val < 330 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c3 : ∀ (c : ZMod 2) (F : Fin 865), 330 ≤ F.val → F.val < 440 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c4 : ∀ (c : ZMod 2) (F : Fin 865), 440 ≤ F.val → F.val < 550 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c5 : ∀ (c : ZMod 2) (F : Fin 865), 550 ≤ F.val → F.val < 660 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c6 : ∀ (c : ZMod 2) (F : Fin 865), 660 ≤ F.val → F.val < 770 → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts_c7 : ∀ (c : ZMod 2) (F : Fin 865), 770 ≤ F.val → (nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0) := by decide +kernel
theorem node_facts (c : ZMod 2) (F : Fin 865) :
    nodeAct (Enode c F) (c, F) = toRoot c F ∧
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F ∧
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F ∧
    sigVec (toRoot c F).1 (toRoot c F).2 = 0 := by
  by_cases h0 : F.val < 110
  · exact node_facts_c0 c F (by omega) h0
  by_cases h1 : F.val < 220
  · exact node_facts_c1 c F (by omega) h1
  by_cases h2 : F.val < 330
  · exact node_facts_c2 c F (by omega) h2
  by_cases h3 : F.val < 440
  · exact node_facts_c3 c F (by omega) h3
  by_cases h4 : F.val < 550
  · exact node_facts_c4 c F (by omega) h4
  by_cases h5 : F.val < 660
  · exact node_facts_c5 c F (by omega) h5
  by_cases h6 : F.val < 770
  · exact node_facts_c6 c F (by omega) h6
  exact node_facts_c7 c F (by omega)

theorem Enode_act (c : ZMod 2) (F : Fin 865) : nodeAct (Enode c F) (c, F) = toRoot c F :=
  (node_facts c F).1

theorem toRoot_fixed (c : ZMod 2) (F : Fin 865) :
    toRoot (toRoot c F).1 (toRoot c F).2 = toRoot c F := (node_facts c F).2.1

theorem moCell_toRoot (c : ZMod 2) (F : Fin 865) :
    moCell (toRoot c F).1 (toRoot c F).2 = moCell c F := (node_facts c F).2.2.1

theorem sigVec_toRoot (c : ZMod 2) (F : Fin 865) :
    sigVec (toRoot c F).1 (toRoot c F).2 = 0 := (node_facts c F).2.2.2

/-- **The finite data of the witness `moWit`**: the types of the listed sides sum to `Enode`, and
all the listed sides are tight at the face. -/
theorem node_wit_facts_c0 : ∀ (c : ZMod 2) (F : Fin 865), 0 ≤ F.val → F.val < 110 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c1 : ∀ (c : ZMod 2) (F : Fin 865), 110 ≤ F.val → F.val < 220 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c2 : ∀ (c : ZMod 2) (F : Fin 865), 220 ≤ F.val → F.val < 330 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c3 : ∀ (c : ZMod 2) (F : Fin 865), 330 ≤ F.val → F.val < 440 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c4 : ∀ (c : ZMod 2) (F : Fin 865), 440 ≤ F.val → F.val < 550 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c5 : ∀ (c : ZMod 2) (F : Fin 865), 550 ≤ F.val → F.val < 660 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c6 : ∀ (c : ZMod 2) (F : Fin 865), 660 ≤ F.val → F.val < 770 → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts_c7 : ∀ (c : ZMod 2) (F : Fin 865), 770 ≤ F.val → ((∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F)) := by decide +kernel
theorem node_wit_facts (c : ZMod 2) (F : Fin 865) :
    (∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F ∧
    (∀ S ∈ (moWit c F).toFinset, Fin.castAdd 24 S ∈ qTight F) := by
  by_cases h0 : F.val < 110
  · exact node_wit_facts_c0 c F (by omega) h0
  by_cases h1 : F.val < 220
  · exact node_wit_facts_c1 c F (by omega) h1
  by_cases h2 : F.val < 330
  · exact node_wit_facts_c2 c F (by omega) h2
  by_cases h3 : F.val < 440
  · exact node_wit_facts_c3 c F (by omega) h3
  by_cases h4 : F.val < 550
  · exact node_wit_facts_c4 c F (by omega) h4
  by_cases h5 : F.val < 660
  · exact node_wit_facts_c5 c F (by omega) h5
  by_cases h6 : F.val < 770
  · exact node_wit_facts_c6 c F (by omega) h6
  exact node_wit_facts_c7 c F (by omega)

theorem Enode_wit (c : ZMod 2) (F : Fin 865) :
    (∑ S ∈ (moWit c F).toFinset, Work.FoldInst.sideType S) = Enode c F :=
  (node_wit_facts c F).1

theorem mem_qTight_of_mem_moWit (c : ZMod 2) (F : Fin 865) (S : Fin 24)
    (hS : S ∈ (moWit c F).toFinset) : Fin.castAdd 24 S ∈ qTight F :=
  (node_wit_facts c F).2 S hS

theorem mbarDim_lt_fin (i : Fin 482) : moDim i < 5 := by decide +revert

theorem mbarDim_lt (c : ZMod 2) (F : Fin 865) : moDim (moCell c F) < 5 :=
  mbarDim_lt_fin (moCell c F)


end

end Work.MbarHomology.Mbar
