/-
  `Work.CoreStep.projTop_graph_union_cyl`: the cell-shaped version of
  `Work.CoreStep.projTop_graph_union`, in which the source is intersected with the cylinder
  `Work.WilE7.cyl C` over the base cell `C` instead of with the base condition
  `projFirst n (m+1) z ∈ C`, and the target is written with the graph cells `Work.WilE7.gr`.

  The two descriptions of the intersection agree:

  * `projTop '' (absSet T ∩ {z | projFirst n (m+1) z ∈ C})` is contained in
    `projTop '' absSet T ∩ cyl C` because `Fin.init (projTop n m z) = projFirst n (m+1) z` and
    every point of `absSet T` lies in the cube `cubeC (n+(m+1))`, so the last fibre coordinate --
    which is the vertical coordinate kept by `projTop` -- is bounded by `1` in absolute value;
  * conversely, `y ∈ projTop '' absSet T ∩ cyl C` gives `Fin.init y ∈ C`, and `projTop` is
    injective on the base coordinates, so the preimage point has base in `C`.

  Combined with `projTop_graph_union` (the covering of `projTop '' absSet T` over `C` by the
  graphs of the sections `s j`), this is the statement that the part of the `(n+1)`-projection of
  the piece `T` lying in the cylinder over `C` is exactly the union of the graph cells of the
  vertical sections `vertCoord (s j ·)`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopTransfer
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.CoreStep.projTop_graph_union

namespace Work.CoreStep

/-- `projTop` of an appended point: the base is kept and the vertical coordinate is read off the
fibre part. -/
private lemma projTop_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    Work.WilE7.CoreStep.projTop n m (Fin.append x y) =
      Fin.snoc x (Work.WilE7.CoreStep.vertCoord y) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Work.WilE7.CoreStep.projTop_last, Fin.snoc_last]
    simp only [Work.WilE7.CoreStep.vertCoord]
    exact Fin.append_right x y (Fin.last m)
  · intro i'
    rw [Work.WilE7.CoreStep.projTop_castSucc, Fin.snoc_castSucc]
    simp [WilkiesDesign.E.projFirst, Fin.append_left]

/-- Every absolute piece lies in the cube `[-1,1]^N`: `SemiPf.set` contains the cube condition. -/
private lemma absSet_subset_cubeC {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Work.WilE7.MainDesign.absSet S ⊆ WilkiesDesign.E.cubeC N := by
  rintro z ⟨w, hw, rfl⟩
  intro i
  exact hw.1 (Fin.cast (Nat.zero_add N).symm i)

theorem projTop_graph_union_cyl {n m k : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      Fin.append x (s j x) ∈ Work.WilE7.MainDesign.absSet T)
    (hcov : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z) :
    Work.WilE7.CoreStep.projTop n m '' Work.WilE7.MainDesign.absSet T ∩ Work.WilE7.cyl C =
      ⋃ j : Fin k, Work.WilE7.gr C (fun x => Work.WilE7.CoreStep.vertCoord (s j x)) := by
  ext y
  constructor
  · -- a projected piece point over `C`: its vertical coordinate is a fibre coordinate over `x`
    rintro ⟨⟨z, hz, rfl⟩, hycyl⟩
    have hC : WilkiesDesign.E.projFirst n (m + 1) z ∈ C := by
      rw [← Work.WilE7.CoreStep.projTop_init]; exact hycyl.1
    obtain ⟨j, hj⟩ := hcov z hz hC
    refine Set.mem_iUnion.2 ⟨j, hycyl.1, ?_⟩
    rw [Work.WilE7.CoreStep.projTop_init]
    change Work.WilE7.CoreStep.projTop n m z (Fin.last n) =
      Work.WilE7.CoreStep.vertCoord (s j (WilkiesDesign.E.projFirst n (m + 1) z))
    rw [hj, Work.WilE7.CoreStep.projTop_last]
    simp only [Work.WilE7.CoreStep.vertCoord]
  · -- conversely, a graph point over `C` is the projection of the point obtained by appending `s j`
    intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨j, hjc, hjlast⟩ := hy
    have hjlast' : y (Fin.last n) = Work.WilE7.CoreStep.vertCoord (s j (Fin.init y)) := hjlast
    refine ⟨⟨Fin.append (Fin.init y) (s j (Fin.init y)), hsub j (Fin.init y) hjc, ?_⟩, ?_⟩
    · rw [projTop_append, ← hjlast']
      exact Fin.snoc_init_self y
    · -- the cylinder bound is automatic: it is the last fibre coordinate of a point of the piece
      refine ⟨hjc, ?_⟩
      rw [hjlast']
      have hz : Fin.append (Fin.init y) (s j (Fin.init y)) ∈
          WilkiesDesign.E.cubeC (n + (m + 1)) :=
        absSet_subset_cubeC T (hsub j (Fin.init y) hjc)
      have hb := hz (Fin.natAdd n (Fin.last m))
      rw [Fin.append_right] at hb
      simpa [Work.WilE7.CoreStep.vertCoord] using hb

end Work.CoreStep
