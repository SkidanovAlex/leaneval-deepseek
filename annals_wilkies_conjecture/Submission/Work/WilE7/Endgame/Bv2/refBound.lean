/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S**: the "height bound" in the form used by the
  vertical row, where the conclusion is directly the union of the sheet graphs.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.hbound_of_frontier_sheets_C
import Submission.Work.WilE7.CoreStep.VerticalG
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.Endgame.E2Aux

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame.Bv2

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)

/-- A sheet graph covers the `projTop`-image of a semi-Pfaffian set over `C`. -/
theorem image_sheet_subset_graph_sheet {p m k : ℕ}
    (X : SemiPf (p + (m + 1))) (C : Set (Fin p → ℝ))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (j : Fin k) (x : Fin p → ℝ), x ∈ C → Fin.append x (s j x) ∈ X.set)
    (hcovS : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z) :
    projTop p m '' X.set ∩ Work.WilE7.cyl C ⊆
      ⋃ j : Fin k, Work.WilE7.gr C (fun x => vertCoord (s j x)) ∩ Work.WilE7.cyl C :=
  Work.WilE7.CoreStep.image_sheet_subset_graph X C (fun i x => vertCoord (s i x)) s hcovS
    (fun j => ⟨j, fun x hx => rfl⟩)

/-- **The height bound, in sheet form.**  The frontier of `projTopSet T` over `C` is contained in
the union of the graphs of the sheets of the covering family `P`. -/
theorem hbound_sheets {n m r : ℕ} (T : Stratum 0 (n + (m + 1))) (C : Set (Fin n → ℝ))
    (P : Fin r → SemiPf (n + (m + 1)))
    (hcov : (closure (absSet T) \ absSet T) ∩
      {z | projFirst n (m + 1) z ∈ C} ⊆ ⋃ e : Fin r, (P e).set)
    (k : Fin r → ℕ) (s : (e : Fin r) → Fin (k e) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (e : Fin r) (j : Fin (k e)) (x : Fin n → ℝ), x ∈ C → Fin.append x (s e j x) ∈ (P e).set)
    (hcovS : ∀ (e : Fin r), ∀ z ∈ (P e).set, projFirst n (m + 1) z ∈ C →
      ∃ j : Fin (k e), s e j (projFirst n (m + 1) z) = projSnd n (m + 1) z) :
    (closure (projTopSet T) \ projTopSet T) ∩ Work.WilE7.cyl C ⊆
      ⋃ e : Fin r, ⋃ j : Fin (k e), Work.WilE7.gr C (fun x => vertCoord (s e j x)) ∩
        Work.WilE7.cyl C := by
  intro y hy
  obtain ⟨hyfront, hycyl⟩ := hy
  obtain ⟨hycl, hynot⟩ := hyfront
  have hstep1 : y ∈ projTop n m '' (closure (absSet T) \ absSet T) :=
    Work.WilE7.CoreStep.closure_diff_projTop_subset n m (Work.CoreStep.absSet_subset_cubeC T)
      ⟨hycl, hynot⟩
  obtain ⟨z, hz, hzy⟩ := hstep1
  have hzC : projFirst n (m + 1) z ∈ C := by
    rw [← Work.WilE7.CoreStep.projTop_init n m z, hzy]; exact hycyl.1
  obtain ⟨e, hze⟩ := Set.mem_iUnion.mp (hcov ⟨hz, hzC⟩)
  have h := image_sheet_subset_graph_sheet (P e) C (s e) (hsub e)
    (fun z' hz' hC' => hcovS e z' hz' hC')
    ⟨⟨z, hze, hzy⟩, hycyl⟩
  obtain ⟨j, hjy⟩ := Set.mem_iUnion.mp h
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨j, hjy⟩⟩

end Work.WilE7.Endgame.Bv2
