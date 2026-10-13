/-
  `Work.WilE7.CoreStep.hbound_of_frontier_sheets_C`.

  The "height bound" step of the `CoreLT_succ` assembly, in the *relative* form: only the part of
  the frontier of `π_{n+1}(T)` lying over the base cell `C` is covered, and correspondingly the
  covering datum `hcov` is only assumed over `C`.

  Compare `hbound_of_frontier_sheets`, which assumes the *global* cover
  `closure (absSet T) \ absSet T ⊆ ⋃ e, (P e).set`.  Here we assume only
  `(closure (absSet T) \ absSet T) ∩ {z | projFirst n (m+1) z ∈ C} ⊆ ⋃ e, (P e).set`.
  That is exactly enough: a point `y` of the frontier of `projTopSet T` lying in `cyl C` lifts to
  `z ∈ closure (absSet T) \ absSet T` with `projTop n m z = y`, and then
  `projFirst n (m+1) z = Fin.init (projTop n m z) = Fin.init y ∈ C` because `y ∈ cyl C`.  So `z`
  lies in the restricted frontier, `hcov` places it in some `P e`, and the sheet/level data
  (`hcovS`, `hlevel`) turn that into a graph cell `gr C (tt i)`.

  The argument is therefore the same three steps as in the absolute case:

  * `closure_diff_projTop_subset` (BV's frontier-of-the-projection identity): the part of
    `closure (projTop '' absSet T)` outside `projTop '' absSet T` comes from
    `closure (absSet T) \ absSet T`.
  * the base coordinate of that lifted point lies in `C` (from `y ∈ cyl C`), so the relative
    covering datum `hcov` applies;
  * for fixed `e`, a point of `projTop '' (P e).set ∩ cyl C` has base in `C`, so `hcovS` picks a
    section `s e j` whose value at that base is the fibre point, and `hlevel` identifies its
    vertical coordinate with some `tt i`; hence the point lies on `gr C (tt i)`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.hbound_of_frontier_sheets
import Submission.Work.WilE7.CoreStep.image_sheet_subset_graph
import Submission.Work.CoreStep.hcof_of_pairCovers

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

theorem hbound_of_frontier_sheets_C {n m K r : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (tt : Fin K → (Fin n → ℝ) → ℝ)
    (P : Fin r → WilkiesDesign.E.SemiPf (n + (m + 1)))
    (hcov : (closure (Work.WilE7.MainDesign.absSet T) \ Work.WilE7.MainDesign.absSet T) ∩
      {z | WilkiesDesign.E.projFirst n (m + 1) z ∈ C} ⊆ ⋃ e : Fin r, (P e).set)
    (k : Fin r → ℕ) (s : (e : Fin r) → Fin (k e) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (e : Fin r) (j : Fin (k e)), ∀ x ∈ C, Fin.append x (s e j x) ∈ (P e).set)
    (hcovS : ∀ (e : Fin r), ∀ z ∈ (P e).set,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
        ∃ j : Fin (k e), s e j (WilkiesDesign.E.projFirst n (m + 1) z) =
          WilkiesDesign.E.projSnd n (m + 1) z)
    (hlevel : ∀ (e : Fin r) (j : Fin (k e)), ∃ i : Fin K, ∀ x ∈ C,
      tt i x = Work.WilE7.CoreStep.vertCoord (s e j x)) :
    (closure (Work.WilE7.CoreStep.projTopSet T) \ Work.WilE7.CoreStep.projTopSet T) ∩
        Work.WilE7.cyl C ⊆
      ⋃ i : Fin K, Work.WilE7.gr C (tt i) ∩ Work.WilE7.cyl C := by
  intro y hy
  obtain ⟨hyfront, hycyl⟩ := hy
  obtain ⟨hycl, hynot⟩ := hyfront
  -- Step 1: the frontier of the projection comes from the frontier of the piece.
  have hstep1 : y ∈ projTop n m ''
      (closure (Work.WilE7.MainDesign.absSet T) \ Work.WilE7.MainDesign.absSet T) :=
    closure_diff_projTop_subset n m (Work.CoreStep.absSet_subset_cubeC T) ⟨hycl, hynot⟩
  obtain ⟨z, hz, hzy⟩ := hstep1
  -- The lifted frontier point has its base in `C`, since `y ∈ cyl C`.
  have hzC : WilkiesDesign.E.projFirst n (m + 1) z ∈ C := by
    rw [← projTop_init n m z, hzy]; exact hycyl.1
  -- Step 2: the (relative) cover places the lifted point in some semi-Pfaffian set `P e`.
  have hzcov : z ∈ ⋃ e : Fin r, (P e).set := hcov ⟨hz, hzC⟩
  rw [Set.mem_iUnion] at hzcov
  obtain ⟨e, hze⟩ := hzcov
  -- Step 3: over `C`, the projected `P e` is covered by the graphs of the levels `tt i`.
  exact image_sheet_subset_graph (P e) C tt (s e)
    (fun z' hz' hC' => hcovS e z' hz' hC') (fun j => hlevel e j)
    ⟨⟨z, hze, hzy⟩, hycyl⟩

end Work.WilE7.CoreStep
