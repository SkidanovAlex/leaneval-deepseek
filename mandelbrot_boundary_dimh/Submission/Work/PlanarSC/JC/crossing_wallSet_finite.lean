import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.Cells

/-!
# Finiteness of the set of crossing times of a generic ray with the wall set

The wall set `wallSet A` of a finite family of lattice cells is the union of finitely many
closed unit grid segments, each of which is horizontal or vertical.  The ray
`t ↦ rayPt a ε t = a + t·(1 + εI)` has direction `1 + εI` with positive imaginary part
`ε > 0`, hence is neither horizontal nor vertical, so it meets every such segment in at most
one point.  Consequently the set of `t > 0` for which the ray point lies in `wallSet A` is
finite.

The proof is by covering `wallSet A` by the four edges of the (finitely many) cells of `A`:
every wall segment bounds a cell of `A`, and each edge is a horizontal or vertical unit
segment.  For a fixed edge the set of crossing times is contained in a singleton.
-/

namespace Work.PlanarSC.JC

open Set
open Work.HornSC.CellBoundaryJordan

/-- The union of the four unit grid edges bounding the closed cell at `p`. -/
def cellEdges (p : ℤ × ℤ) : Set ℂ :=
  hSeg (p.1, p.2) ∪ hSeg (p.1, p.2 + 1) ∪ vSeg (p.1, p.2) ∪ vSeg (p.1 + 1, p.2)

/-- The ray meets a horizontal unit grid segment in at most one point: for such a point the time
`t` is forced to be `(u.2 - a.im)/ε`. -/
lemma rayPt_preimage_hSeg_finite {a : ℂ} {ε : ℝ} (hε : ε ≠ 0) (u : ℤ × ℤ) :
    {t : ℝ | rayPt a ε t ∈ hSeg u}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton (((u.2 : ℝ) - a.im) / ε)) ?_
  intro t ht
  rw [Set.mem_ofPred_eq, mem_hSeg] at ht
  rw [Set.mem_singleton_iff]
  have him : ε * t = (u.2 : ℝ) - a.im := by
    have h := ht.1; rw [rayPt_im] at h; linarith
  rw [eq_div_iff hε]
  linarith

/-- The ray meets a vertical unit grid segment in at most one point: for such a point the time
`t` is forced to be `u.1 - a.re`. -/
lemma rayPt_preimage_vSeg_finite {a : ℂ} {ε : ℝ} (u : ℤ × ℤ) :
    {t : ℝ | rayPt a ε t ∈ vSeg u}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton ((u.1 : ℝ) - a.re)) ?_
  intro t ht
  rw [Set.mem_ofPred_eq, mem_vSeg] at ht
  rw [Set.mem_singleton_iff]
  have h := ht.1; rw [rayPt_re] at h; linarith

/-- The set of times at which the ray lies on one of the four edges of the cell at `p` is
finite. -/
lemma rayPt_preimage_cellEdges_finite {a : ℂ} {ε : ℝ} (hε : ε ≠ 0) (p : ℤ × ℤ) :
    {t : ℝ | rayPt a ε t ∈ cellEdges p}.Finite := by
  have h1 := rayPt_preimage_hSeg_finite (a := a) hε (p.1, p.2)
  have h2 := rayPt_preimage_hSeg_finite (a := a) hε (p.1, p.2 + 1)
  have h3 := rayPt_preimage_vSeg_finite (ε := ε) (a := a) (p.1, p.2)
  have h4 := rayPt_preimage_vSeg_finite (ε := ε) (a := a) (p.1 + 1, p.2)
  have heq : {t : ℝ | rayPt a ε t ∈ cellEdges p} =
      ({t | rayPt a ε t ∈ hSeg (p.1, p.2)} ∪ {t | rayPt a ε t ∈ hSeg (p.1, p.2 + 1)} ∪
       {t | rayPt a ε t ∈ vSeg (p.1, p.2)} ∪ {t | rayPt a ε t ∈ vSeg (p.1 + 1, p.2)}) := by
    ext t; simp only [cellEdges, Set.mem_ofPred_eq, Set.mem_union]
  rw [heq]
  exact ((h1.union h2).union h3).union h4

/-- Every segment of the wall set of `A` is one of the four edges of a cell of `A`. -/
lemma wallSet_subset_iUnion_cellEdges (A : Finset (ℤ × ℤ)) :
    wallSet A ⊆ ⋃ p ∈ (A : Set (ℤ × ℤ)), cellEdges p := by
  intro z hz
  rw [mem_wallSet] at hz
  rcases hz with ⟨u, hw, hzu⟩ | ⟨u, hw, hzu⟩
  · rcases hw with ⟨h1, _⟩ | ⟨_, h2⟩
    · -- `hSeg u` is the lower edge of the cell `(u.1, u.2) ∈ A`
      refine Set.mem_iUnion₂.mpr ⟨u, h1, ?_⟩
      change z ∈ (hSeg (u.1, u.2) ∪ hSeg (u.1, u.2 + 1) ∪
        vSeg (u.1, u.2) ∪ vSeg (u.1 + 1, u.2))
      exact Or.inl (Or.inl (Or.inl hzu))
    · -- `hSeg u` is the upper edge of the cell `(u.1, u.2 - 1) ∈ A`
      refine Set.mem_iUnion₂.mpr ⟨(u.1, u.2 - 1), h2, ?_⟩
      have hpu : (((u.1, u.2 - 1) : ℤ × ℤ).1, ((u.1, u.2 - 1) : ℤ × ℤ).2 + 1) = u := by
        ext <;> simp
      change z ∈ (hSeg (((u.1, u.2 - 1) : ℤ × ℤ).1, ((u.1, u.2 - 1) : ℤ × ℤ).2)
        ∪ hSeg (((u.1, u.2 - 1) : ℤ × ℤ).1, ((u.1, u.2 - 1) : ℤ × ℤ).2 + 1)
        ∪ vSeg (((u.1, u.2 - 1) : ℤ × ℤ).1, ((u.1, u.2 - 1) : ℤ × ℤ).2)
        ∪ vSeg (((u.1, u.2 - 1) : ℤ × ℤ).1 + 1, ((u.1, u.2 - 1) : ℤ × ℤ).2))
      rw [hpu]
      exact Or.inl (Or.inl (Or.inr hzu))
  · rcases hw with ⟨h1, _⟩ | ⟨_, h2⟩
    · -- `vSeg u` is the left edge of the cell `(u.1, u.2) ∈ A`
      refine Set.mem_iUnion₂.mpr ⟨u, h1, ?_⟩
      change z ∈ (hSeg (u.1, u.2) ∪ hSeg (u.1, u.2 + 1) ∪
        vSeg (u.1, u.2) ∪ vSeg (u.1 + 1, u.2))
      exact Or.inl (Or.inr hzu)
    · -- `vSeg u` is the right edge of the cell `(u.1 - 1, u.2) ∈ A`
      refine Set.mem_iUnion₂.mpr ⟨(u.1 - 1, u.2), h2, ?_⟩
      have hpu : (((u.1 - 1, u.2) : ℤ × ℤ).1 + 1, ((u.1 - 1, u.2) : ℤ × ℤ).2) = u := by
        ext <;> simp
      change z ∈ (hSeg (((u.1 - 1, u.2) : ℤ × ℤ).1, ((u.1 - 1, u.2) : ℤ × ℤ).2)
        ∪ hSeg (((u.1 - 1, u.2) : ℤ × ℤ).1, ((u.1 - 1, u.2) : ℤ × ℤ).2 + 1)
        ∪ vSeg (((u.1 - 1, u.2) : ℤ × ℤ).1, ((u.1 - 1, u.2) : ℤ × ℤ).2)
        ∪ vSeg (((u.1 - 1, u.2) : ℤ × ℤ).1 + 1, ((u.1 - 1, u.2) : ℤ × ℤ).2))
      rw [hpu]
      exact Or.inr hzu

theorem crossing_wallSet_finite (A : Finset (ℤ × ℤ)) {a : ℂ} {ε : ℝ} (hε : 0 < ε) :
    {t : ℝ | 0 < t ∧ Work.HornSC.CellBoundaryJordan.rayPt a ε t ∈
      Work.HornSC.CellBoundaryJordan.wallSet A}.Finite := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcell : ∀ p ∈ (A : Set (ℤ × ℤ)), {t : ℝ | rayPt a ε t ∈ cellEdges p}.Finite :=
    fun p _ => rayPt_preimage_cellEdges_finite hεne p
  have hU : (⋃ p ∈ (A : Set (ℤ × ℤ)), {t : ℝ | rayPt a ε t ∈ cellEdges p}).Finite :=
    Set.Finite.biUnion A.finite_toSet hcell
  refine hU.subset ?_
  intro t ht
  obtain ⟨_, hmem⟩ := ht
  obtain ⟨p, hpA, hpz⟩ := Set.mem_iUnion₂.mp (wallSet_subset_iUnion_cellEdges A hmem)
  exact Set.mem_iUnion₂.mpr ⟨p, hpA, hpz⟩

end Work.PlanarSC.JC
