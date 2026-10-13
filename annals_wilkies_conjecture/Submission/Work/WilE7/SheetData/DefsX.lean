/-
  `Work.WilE7.SheetData.DefsX`: the `SheetData` vocabulary of the sheet-component lemma.

  The file `Submission/Work/WilE7/graphCell_bd.lean` proves the graph-cell piece lemma for an
  arbitrary `Good` stratum `S : Stratum p (m+1)` with `S.j = m+1`.  Its proof, and the proof of
  the sheet-component lemma `Work.WilE7.sheetComponentGen` it rests on, use the stratum `S` only
  through the underlying semi-Pfaffian set `S.X` — the `Good` hypothesis and the value of `S.j`
  are never touched.

  This module isolates that dependence: `sheetProductX p q Z X` is the fibre product of `Z` with
  the *semi-Pfaffian set* `X` (no stratum involved), and it agrees definitionally with
  `Work.WilE7.sheetProduct p q Z S` whenever `S.X = X`, and with the set of the semi-Pfaffian set
  `Work.WilE7.fiberProdZ Z X`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.SheetComponentDefs
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.sheetComponent

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.SheetData
open WilkiesDesign WilkiesDesign.E

/-- The fibre product of the semi-Pfaffian sets `Z, X ⊆ ℝ^{p+q}` over their common base `ℝ^p`,
sitting in `ℝ^{(p+q)+(p+q)}`.  This is `Work.WilE7.sheetProduct p q Z S` with `S.X` replaced by
`X`. -/
def sheetProductX (p q : ℕ) (Z X : SemiPf (p + q)) : Set (Fin ((p + q) + (p + q)) → ℝ) :=
  {z | projFirst (p + q) (p + q) z ∈ Z.set ∧ projSnd (p + q) (p + q) z ∈ X.set ∧
    projFirst p q (projFirst (p + q) (p + q) z) =
      projFirst p q (projSnd (p + q) (p + q) z)}

/-- Membership in `sheetProductX`, unfolded. -/
theorem mem_sheetProductX {p q : ℕ} {Z X : SemiPf (p + q)}
    {z : Fin ((p + q) + (p + q)) → ℝ} :
    z ∈ sheetProductX p q Z X ↔
      projFirst (p + q) (p + q) z ∈ Z.set ∧ projSnd (p + q) (p + q) z ∈ X.set ∧
        projFirst p q (projFirst (p + q) (p + q) z) =
          projFirst p q (projSnd (p + q) (p + q) z) := Iff.rfl

/-- The set of the semi-Pfaffian fibre product `fiberProdZ Z X` is `sheetProductX p q Z X`. -/
theorem sheetProductX_eq_fiberProdZ_set (p q : ℕ) (Z X : SemiPf (p + q)) :
    sheetProductX p q Z X = (Work.WilE7.fiberProdZ Z X).set := by
  rw [Work.WilE7.fiberProdZ_set]
  rfl

/-- The part of the fibre product whose base projection lies in `C`. -/
def sheetBaseX (p q : ℕ) (Z X : SemiPf (p + q)) (C : Set (Fin p → ℝ)) :
    Set (Fin ((p + q) + (p + q)) → ℝ) :=
  {z | z ∈ sheetProductX p q Z X ∧ projFirst p q (projSnd (p + q) (p + q) z) ∈ C}

/-- Membership in `sheetBaseX`, unfolded. -/
theorem mem_sheetBaseX {p q : ℕ} {Z X : SemiPf (p + q)} {C : Set (Fin p → ℝ)}
    {z : Fin ((p + q) + (p + q)) → ℝ} :
    z ∈ sheetBaseX p q Z X C ↔
      z ∈ sheetProductX p q Z X ∧ projFirst p q (projSnd (p + q) (p + q) z) ∈ C := Iff.rfl

/-- **Base projection of the fibre-product component.**  Every point of the component of
`w₀ = (u₀, (π u₀, s j (π u₀)))` in the fibre product bases over `C`.  This is
`Work.WilE7.GraphCellAux.sheetProduct_base_mem` with the stratum `S` replaced by the
semi-Pfaffian set `X`. -/
theorem sheetProductX_base_mem {p q : ℕ} (X Z : SemiPf (p + q)) (u₀ : Fin (p + q) → ℝ)
    (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p q) (connectedComponentIn Z.set u₀))
    {k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k) :
    ∀ z ∈ connectedComponentIn (sheetProductX p q Z X)
        (Work.WilE7.sheetProductPt u₀ s j),
      projFirst p q (projFirst (p + q) (p + q) z) ∈ C := by
  have _ := hu₀
  by_cases hw : Work.WilE7.sheetProductPt u₀ s j ∈ sheetProductX p q Z X
  · intro z hz
    have hmem : projFirst (p + q) (p + q) z ∈ connectedComponentIn Z.set u₀ := by
      have h := Work.WilE7.imageSubsetConnectedComponentIn
        (s := connectedComponentIn (sheetProductX p q Z X) (Work.WilE7.sheetProductPt u₀ s j))
        isPreconnected_connectedComponentIn
        (continuous_projFirst (p + q) (p + q)).continuousOn
        (x := Work.WilE7.sheetProductPt u₀ s j) (mem_connectedComponentIn hw)
        (F := Z.set) (fun y hy => (mem_sheetProductX.mp
          (connectedComponentIn_subset _ _ hy)).1) z hz
      rwa [Work.WilE7.projFirst_sheetProductPt] at h
    rw [hC]
    exact ⟨_, hmem, rfl⟩
  · intro z hz
    rw [connectedComponentIn_eq_empty hw] at hz
    exact absurd hz (by simp)

end Work.WilE7.SheetData
