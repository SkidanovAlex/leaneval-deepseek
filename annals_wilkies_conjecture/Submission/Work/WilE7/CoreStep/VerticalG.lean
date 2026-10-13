/-
  `Work.WilE7.CoreStep.VerticalG`: the part of the **vertical row** of `CoreLT_succ` that is
  *free* from the `Σ`-avoidance data.

  Setup (the `(n, m+1)` frame, vertical = last fibre coordinate, `π_{n+1} = projTop`): `T` is an
  absolute piece and `C` a base cell that *avoids the projection of the topological frontier of
  `T`* — this is exactly the hypothesis `Work.CoreStep.hclosed` produced by clause (3) of
  `sigmaFamily` (the frontier sets of the pieces) together with the `Σ`-disjointness of the cell:

      `hclosed : ∀ z ∈ closure (absSet T), projFirst n (m+1) z ∈ C → z ∈ absSet T`.

  Three consequences are proved here; all three are used by the per-cell case analysis of
  `CoreLT_succ` (see `NOTES_S50_vertical_row_G_case.md`).

  * `absSet_subset_cubeC` — every absolute piece lies in the cube (an ambient fact used to invoke
    `closure_projTop_subset`).
  * `projTopSet_closure_subset_of_hclosed` — **`A := projTopSet T ∩ cyl C` is *closed* in
    `cyl C`**, i.e. `closure (projTopSet T) ∩ cyl C ⊆ projTopSet T`.  (Consequence: the sections
    `J(x) = vertCoord '' (π_n-fibre of T over x)` are closed and every `Σ`-free cell is *not* a
    "boundary" cell in the sense of `NOTES_S49` §3 — the example there has `C ⊆ π_n(∂T)`, hence is
    a Σ-cell.)
  * `sheet_mem_absSet_of_hclosed`, `mem_projTopSet_of_sheet` — **every sheet of every graph-like
    piece `P ⊆ closure (absSet T)` active over `C` has *all* its points in `absSet T`**, hence
    *every* level graph `gr C (tt i)` of such a sheet is *contained in* `A` (the first alternative
    of the `hgraph` hypothesis of `cells_compat_levels`).
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.ProjTopFrontier
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.cylDecomp_union
import Submission.Work.WilE7.CoreStep.FibreEndDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- Every absolute piece lies in the cube `[-1,1]^N`.  (`absSet` is the image of `X.set` under the
reindexing `absPt`, and the cube bound is part of every semi-Pfaffian set.) -/
theorem absSet_subset_cubeC {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Work.WilE7.MainDesign.absSet S ⊆ WilkiesDesign.E.cubeC N := by
  rintro z ⟨w, hw, hweq⟩
  rw [← hweq]
  intro i
  exact hw.1 (Fin.cast (Nat.zero_add N).symm i)

/-- **The `projTop`-image of a piece is closed over a cell avoiding the projection of the
frontier.**  This is the `hclosed` form of the `Σ`-avoidance: every limit point (with base in `C`)
of `projTopSet T` already lies in `projTopSet T`; equivalently `A = projTopSet T ∩ cyl C` is closed
in `cyl C`. -/
theorem projTopSet_closure_inter_cyl_subset_of_hclosed {n m : ℕ}
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))} {C : Set (Fin n → ℝ)}
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T) :
    closure (projTopSet T) ∩ Work.WilE7.cyl C ⊆ projTopSet T := by
  intro p hp
  obtain ⟨hpcl, hpcyl⟩ := hp
  have hcl := closure_projTop_subset n m (absSet_subset_cubeC T) hpcl
  obtain ⟨z, hz, hzp⟩ := hcl
  have hzC : WilkiesDesign.E.projFirst n (m + 1) z ∈ C := by
    have h1 : Fin.init (projTop n m z) = WilkiesDesign.E.projFirst n (m + 1) z := projTop_init n m z
    rw [← h1, hzp]
    exact hpcyl.1
  exact ⟨z, hclosed z hz hzC, hzp⟩

/-- A closed-in-the-subspace form of the previous lemma. -/
theorem isClosed_projTopSet_inter {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    {C : Set (Fin n → ℝ)}
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T) :
    IsClosed {z : ↥(Work.WilE7.cyl C) | (z : Fin (n + 1) → ℝ) ∈ projTopSet T} := by
  rw [isClosed_induced_iff]
  refine ⟨closure (projTopSet T), isClosed_closure, ?_⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · intro hz
    exact projTopSet_closure_inter_cyl_subset_of_hclosed hclosed ⟨hz, z.2⟩
  · intro hz
    exact subset_closure hz

/-- **Every sheet of a graph-like piece inside `closure (absSet T)` over a frontier-avoiding cell
lies in `absSet T`.**  Immediate from `hclosed`: a sheet point of `P` is a point of
`closure (absSet T)` whose base projection is in `C`. -/
theorem sheet_mem_absSet_of_hclosed {n m k : ℕ}
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))} {C : Set (Fin n → ℝ)}
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    {P : WilkiesDesign.E.SemiPf (n + (m + 1))}
    (hP : P.set ⊆ closure (Work.WilE7.MainDesign.absSet T))
    (s : Fin k → (Fin n → ℝ) → Fin (m + 1) → ℝ)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ P.set) :
    ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C → Fin.append x (s j x) ∈ Work.WilE7.MainDesign.absSet T := by
  intro j x hx
  refine hclosed (Fin.append x (s j x)) (hP (hsub j x hx)) ?_
  rw [Work.WilE7.projFirst_append]
  exact hx

/-- The `projTop`-image of an appended point: the vertical coordinate of the appended fibre point
is the last coordinate. -/
theorem projTop_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    projTop n m (Fin.append x y) = Fin.snoc x (y (Fin.last m)) := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · rw [projTop_last, Work.WilE7.projSnd_append]
    simp only [Fin.snoc_last]
  · intro i'
    rw [projTop_castSucc, Work.WilE7.projFirst_append]
    simp only [Fin.snoc_castSucc]

/-- **The first alternative of `hgraph` is free in the frontier-avoiding (`Σ`-free) case**: the
level graph of a sheet of a graph-like piece `P ⊆ closure (absSet T)` over `C` is *contained in*
`A = projTopSet T ∩ cyl C`. -/
theorem snoc_vertCoord_mem_projTopSet {n m k : ℕ}
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))} {C : Set (Fin n → ℝ)}
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    {P : WilkiesDesign.E.SemiPf (n + (m + 1))}
    (hP : P.set ⊆ closure (Work.WilE7.MainDesign.absSet T))
    (s : Fin k → (Fin n → ℝ) → Fin (m + 1) → ℝ)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ P.set)
    (j : Fin k) {x : Fin n → ℝ} (hx : x ∈ C) :
    Fin.snoc x (vertCoord (s j x)) ∈ projTopSet T := by
  have hmem := sheet_mem_absSet_of_hclosed hclosed hP s hsub j x hx
  rw [show Fin.snoc x (vertCoord (s j x)) = projTop n m (Fin.append x (s j x)) from
    (projTop_append x (s j x)).symm]
  exact ⟨Fin.append x (s j x), hmem, rfl⟩

end Work.WilE7.CoreStep
