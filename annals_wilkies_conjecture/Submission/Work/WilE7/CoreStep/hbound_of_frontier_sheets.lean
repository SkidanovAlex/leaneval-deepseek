/-
  `Work.WilE7.CoreStep.hbound_of_frontier_sheets`.

  The "height bound" step of the `CoreLT_succ` assembly: the part of the frontier of
  `π_{n+1}(T) = projTop '' absSet T` lying in the cylinder `cyl C` over a base cell `C` is covered
  by the graph cells `gr C (tt i)` of a *finite* family of level functions `tt i` on `C`.

  The data are exactly the data produced by the semi-Pfaffian stratification of the frontier of
  the piece together with the sheet selection: semi-Pfaffian sets `P e` covering
  `closure (absSet T) \ absSet T`, and, for every `e`, finitely many continuous sections
  `s e j : C → ℝ^{m+1}` whose graphs lie in `(P e).set` (`hsub`), which cover the fibre of
  `(P e).set` over every point of `C` (`hcovS`), and whose vertical coordinates are among the
  `tt i` on `C` (`hlevel`).

  The argument is in three steps.

  * `closure_diff_projTop_subset` (BV's frontier-of-the-projection identity): the part of
    `closure (projTop '' absSet T)` outside `projTop '' absSet T` comes from
    `closure (absSet T) \ absSet T`, i.e. from the topological frontier of the piece.
  * `hcov`: that frontier is contained in `⋃ e, (P e).set`.
  * For fixed `e`, a point of `projTop '' (P e).set ∩ cyl C` has base in `C`, so `hcovS` picks a
    section `s e j` whose value at that base is the fibre point, and `hlevel` identifies its
    vertical coordinate with some `tt i`; hence the point lies on `gr C (tt i)`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.ProjTopFrontier
import Submission.Work.CoreStep.projTop_graph_union_cyl
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.coreLT_succ.graphUnion_eq_projTop

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- Every absolute piece lies in the cube `[-1,1]^N` (the cube bound is part of every semi-Pfaffian
set, and `absSet` is the image of `X.set` under the reindexing `absPt`). -/
private lemma absSet_subset_cubeC_aux {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Work.WilE7.MainDesign.absSet S ⊆ WilkiesDesign.E.cubeC N := by
  rintro z ⟨w, hw, hweq⟩
  rw [← hweq]
  intro i
  exact hw.1 (Fin.cast (Nat.zero_add N).symm i)

/-- Over the base cell `C`, the `projTop`-image of a semi-Pfaffian set `X`, restricted to `cyl C`,
is covered by the graph cells of the levels `tt i` attained by the vertical sections `s j`. -/
private lemma image_sheet_subset_graph {p m K : ℕ}
    (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (tt : Fin K → (Fin p → ℝ) → ℝ)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (_hsub : ∀ (j : Fin k), ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcovS : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
    (hlevel : ∀ j : Fin k, ∃ i : Fin K, ∀ x ∈ C,
      tt i x = vertCoord (s j x)) :
    projTop p m '' X.set ∩ Work.WilE7.cyl C ⊆
      ⋃ i : Fin K, Work.WilE7.gr C (tt i) ∩ Work.WilE7.cyl C := by
  rintro y ⟨⟨z, hz, hzy⟩, hycyl⟩
  have hyC : Fin.init y ∈ C := hycyl.1
  have hC : WilkiesDesign.E.projFirst p (m + 1) z ∈ C := by
    rw [← projTop_init p m z, hzy]; exact hyC
  obtain ⟨j, hj⟩ := hcovS z hz hC
  obtain ⟨i, hi⟩ := hlevel j
  refine Set.mem_iUnion.2 ⟨i, ⟨?_, hycyl⟩⟩
  have hiny : Fin.init y = WilkiesDesign.E.projFirst p (m + 1) z := by
    rw [← hzy, projTop_init]
  refine ⟨hyC, ?_⟩
  rw [hi (Fin.init y) hyC, hiny, hj, ← hzy, projTop_last]
  rfl

theorem hbound_of_frontier_sheets {n m K r : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (tt : Fin K → (Fin n → ℝ) → ℝ)
    (P : Fin r → WilkiesDesign.E.SemiPf (n + (m + 1)))
    (hcov : closure (Work.WilE7.MainDesign.absSet T) \ Work.WilE7.MainDesign.absSet T ⊆
      ⋃ e : Fin r, (P e).set)
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
    closure_diff_projTop_subset n m (absSet_subset_cubeC_aux T) ⟨hycl, hynot⟩
  obtain ⟨z, hz, hzy⟩ := hstep1
  -- Step 2: the frontier of the piece is covered by the semi-Pfaffian sets `P e`.
  have hzcov : z ∈ ⋃ e : Fin r, (P e).set := hcov hz
  rw [Set.mem_iUnion] at hzcov
  obtain ⟨e, hze⟩ := hzcov
  -- Step 3: over `C`, the projected `P e` is covered by the graphs of the levels `tt i`.
  exact image_sheet_subset_graph (P e) C tt (k e) (s e)
    (fun j x hx => hsub e j x hx) (fun z' hz' hC' => hcovS e z' hz' hC')
    (fun j => hlevel e j) ⟨⟨z, hze, hzy⟩, hycyl⟩

end Work.WilE7.CoreStep
