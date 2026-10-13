/-
  Area E7, dimension-one case of BV Proposition 9: `cuts U` really is a cylindrical
  decomposition of the line `[-1,1]`.

  For a finite set `U ⊆ ℝ` of cut points, `Work.WilE7.cuts U` consists of the singletons
  `{t}` (`t ∈ U`) and the open intervals between consecutive points of `U`
  (`DimOneCells.lean`).  When `-1, 1 ∈ U` and `U ⊆ [-1,1]`, that family partitions the
  cube `cubeC 1 = [-1,1]` into cylindrical cells, which is exactly
  `IsCylDecompOn 1 (cubeC 1) (cuts U)`.

  The three structural halves of the proof are proved (in parallel) in the sibling
  directory `CylAux`:

  * `CylAux.cuts_cell_shapes`      — every cell is `IsCell 1` and nonempty;
  * `CylAux.cuts_pairwiseDisjoint` — distinct cells are disjoint;
  * `CylAux.cuts_cover_cube`       — the cells cover the cube.

  Here we assemble them, together with the dimension-zero base case of the recursive
  definition of `IsCylDecompOn` (over the one-point space `ℝ⁰ = Fin 0 → ℝ`).
-/
import Mathlib
import Submission.Work.WilE7.DimOneCells
import Submission.Work.WilE7.CylAux.cuts_pairwiseDisjoint
import Submission.Work.WilE7.CylAux.cuts_cover_cube
import Submission.Work.WilE7.CylAux.cuts_cell_shapes

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The dimension-zero base case -/

/-- The space `ℝ⁰ = Fin 0 → ℝ` is a single point, so the projection `Fin.init` of any
nonempty subset of `ℝ¹ = Fin 1 → ℝ` is everything. -/
theorem fin_init_image_eq_univ₁ {κ : Set (Fin 1 → ℝ)} (h : κ.Nonempty) :
    Fin.init '' κ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, Subsingleton.elim _ _⟩

/-- The projection of the cube `[-1,1] ⊆ ℝ¹` to `ℝ⁰` is everything. -/
theorem fin_init_cubeC_one : Fin.init '' (cubeC 1 : Set (Fin 1 → ℝ)) = Set.univ :=
  fin_init_image_eq_univ₁ ⟨pt1 0, fun i => by simp [pt1]⟩

/-- The projection of the cell family `cuts U` (with `U` nonempty) down to `ℝ⁰`: every cell
is nonempty, hence projects onto the single point of `ℝ⁰`, so the image is `{univ}`. -/
theorem cuts_image_init {U : Finset ℝ} (hU : U.Nonempty) :
    (cuts U).image (fun c => Fin.init '' c) = {Set.univ} := by
  obtain ⟨t, ht⟩ := hU
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨cellPt t, mem_cuts.mpr (Or.inl ⟨t, ht, rfl⟩),
      fin_init_image_eq_univ₁ (cellPt_nonempty t)⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨c, hc, rfl⟩
    exact fin_init_image_eq_univ₁ ((CylAux.cuts_cell_shapes U c hc).2)

/-- The dimension-zero clause of `IsCylDecompOn`, for the family `cuts U` and the cube
`[-1,1]` (needs only `U ≠ ∅`). -/
theorem cylDecompOn_zero_of_cuts {U : Finset ℝ} (hU : U.Nonempty) :
    IsCylDecompOn 0 (Fin.init '' (cubeC 1 : Set (Fin 1 → ℝ)))
      ((cuts U).image (fun c => Fin.init '' c)) := by
  left
  exact ⟨fin_init_cubeC_one, cuts_image_init hU⟩

/-! ## The theorem -/

theorem DimOneCellsCyl (U : Finset ℝ) (hneg : (-1 : ℝ) ∈ U) (hpos : (1 : ℝ) ∈ U)
    (hU : ∀ t ∈ U, |t| ≤ 1) :
    WilkiesDesign.E.IsCylDecompOn 1 (WilkiesDesign.E.cubeC 1) (Work.WilE7.cuts U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CylAux.cuts_cell_shapes U
  · exact CylAux.cuts_pairwiseDisjoint U
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨κ, hκ, hxκ⟩ := Set.mem_sUnion.mp hx
      exact cuts_subset_cube hU κ hκ hxκ
    · exact CylAux.cuts_cover_cube U hneg hpos
  · exact cylDecompOn_zero_of_cuts ⟨-1, hneg⟩

end Work.WilE7
