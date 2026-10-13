/-
  `Work.WilE7.coreLT_succ.graphUnion_eq_projTop`: the covering of the `(p+1)`-projection of the
  semi-Pfaffian set `X` restricted to the cylinder over `C` by the graphs of the vertical sections
  `s j` (the cell-shaped statement actually used in the `CoreLT_succ` assembly).

  This is the `SemiPf`-level analogue of `Work.CoreStep.projTop_graph_union_cyl` (which is phrased
  for an abstract stratum via `Work.WilE7.MainDesign.absSet`); here the source is a `SemiPf` set
  `X` in `ℝ^{p+(m+1)}` and the graph cells are written out directly.

  Forward: a graph point `y` over `C` is `projTop` of the point `Fin.append (Fin.init y) (s j ·)`,
  which lies in `X.set` by `hmem`; the cylinder bound on the last coordinate is automatic because
  it is a coordinate of a point of `X.set ⊆ cubeC`.  Backward: a point `y` of
  `projTop '' X.set ∩ cyl C` comes from some `z ∈ X.set` with `Fin.init y = projFirst p (m+1) z ∈ C`,
  so `hcov` produces the matching index `j`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.DecompDefs
import Submission.Work.CoreStep.projTop_graph_union_cyl

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E

/-- `projTop` of an appended point: the base is kept and the vertical coordinate is read off the
fibre part. -/
private lemma projTop_append {p m : ℕ} (x : Fin p → ℝ) (y : Fin (m + 1) → ℝ) :
    Work.WilE7.CoreStep.projTop p m (Fin.append x y) =
      Fin.snoc x (Work.WilE7.CoreStep.vertCoord y) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Work.WilE7.CoreStep.projTop_last, Fin.snoc_last]
    simp only [Work.WilE7.CoreStep.vertCoord]
    exact Fin.append_right x y (Fin.last m)
  · intro i'
    rw [Work.WilE7.CoreStep.projTop_castSucc, Fin.snoc_castSucc]
    simp [WilkiesDesign.E.projFirst, Fin.append_left]

/-- Every semi-Pfaffian set is contained in the cube it is defined in. -/
private lemma semiPf_set_subset_cube {k : ℕ} (X : WilkiesDesign.E.SemiPf k) :
    WilkiesDesign.E.SemiPf.set X ⊆ WilkiesDesign.E.cubeC k := fun _ hx => hx.1

theorem graphUnion_eq_projTop {p m : ℕ} (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hmem : ∀ (j : Fin k) (x : Fin p → ℝ), x ∈ C →
      Fin.append x (s j x) ∈ WilkiesDesign.E.SemiPf.set X)
    (hcov : ∀ z ∈ WilkiesDesign.E.SemiPf.set X,
      WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z) :
    (⋃ j : Fin k, {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        y (Fin.last p) = s j (Fin.init y) (Fin.last m)})
      = Work.WilE7.CoreStep.projTop p m '' (WilkiesDesign.E.SemiPf.set X) ∩ Work.WilE7.cyl C := by
  ext y
  constructor
  · -- a graph point over `C` is the projection of the appended point `Fin.append (Fin.init y) (s j ·)`
    intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨j, hjc, hjlast⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [Set.mem_image]
      refine ⟨Fin.append (Fin.init y) (s j (Fin.init y)), hmem j (Fin.init y) hjc, ?_⟩
      rw [projTop_append]
      simp only [Work.WilE7.CoreStep.vertCoord]
      rw [← hjlast]
      exact Fin.snoc_init_self y
    · -- the cylinder bound is automatic: it is the last fibre coordinate of a point of `X.set`
      rw [Work.WilE7.cyl]
      refine ⟨hjc, ?_⟩
      have hz : Fin.append (Fin.init y) (s j (Fin.init y)) ∈ WilkiesDesign.E.cubeC (p + (m + 1)) :=
        semiPf_set_subset_cube X (hmem j (Fin.init y) hjc)
      have hb := hz (Fin.natAdd p (Fin.last m))
      rw [Fin.append_right] at hb
      rw [hjlast]
      simpa [Work.WilE7.CoreStep.vertCoord] using hb
  · -- a projected point over `C` has its vertical coordinate equal to a fibre coordinate over `x`
    rintro ⟨himg, hycyl⟩
    rw [Set.mem_image] at himg
    obtain ⟨z, hz, hzy⟩ := himg
    rw [Work.WilE7.cyl] at hycyl
    obtain ⟨hyC, -⟩ := hycyl
    have hC : WilkiesDesign.E.projFirst p (m + 1) z ∈ C := by
      rw [← Work.WilE7.CoreStep.projTop_init, hzy]
      exact hyC
    obtain ⟨j, hj⟩ := hcov z hz hC
    refine Set.mem_iUnion.2 ⟨j, hyC, ?_⟩
    rw [← hzy, Work.WilE7.CoreStep.projTop_last, Work.WilE7.CoreStep.projTop_init]
    rw [hj]

end Work.WilE7.coreLT_succ
