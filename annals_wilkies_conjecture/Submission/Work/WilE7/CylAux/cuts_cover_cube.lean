import Mathlib
import Submission.Work.WilE7.DimOneCells

namespace Work.WilE7.CylAux

open Classical
open Work.WilE7

/-- Every point of the line `cubeC 1 = [-1,1]` lies in one of the cells cut out by `U`, as soon
as `-1` and `1` belong to `U`: either the first coordinate is itself in `U` (a singleton cell),
or it lies strictly between the largest element of `U` below it and the smallest element of `U`
above it, and these two are consecutive because of the way they were chosen. -/
theorem cuts_cover_cube (U : Finset ℝ) (hneg : (-1 : ℝ) ∈ U) (hpos : (1 : ℝ) ∈ U) :
    WilkiesDesign.E.cubeC 1 ⊆ ⋃₀ (↑(Work.WilE7.cuts U) : Set (Set (Fin 1 → ℝ))) := by
  intro x hx
  rw [Set.mem_sUnion]
  by_cases hxU : x 0 ∈ U
  · -- `x` is a cut point: the singleton cell `{x}` covers it.
    refine ⟨cellPt (x 0), ?_, ?_⟩
    · rw [Finset.mem_coe, mem_cuts]; exact Or.inl ⟨x 0, hxU, rfl⟩
    · rw [mem_cellPt, pt1_eq_iff]
  · -- `x` is not a cut point: it lies strictly inside the interval between the neighbouring
    -- cut points of `U`.  Since `-1, 1 ∈ U`, both neighbours exist.
    have hx0 : |x 0| ≤ 1 := hx 0
    have hle := abs_le.mp hx0
    have hlt_neg : (-1 : ℝ) < x 0 := by
      rcases lt_or_eq_of_le hle.1 with h | h
      · exact h
      · exact absurd (h ▸ hneg) hxU
    have hlt_pos : x 0 < 1 := by
      rcases lt_or_eq_of_le hle.2 with h | h
      · exact h
      · exact absurd (h ▸ hpos) hxU
    set A : Finset ℝ := U.filter (fun u => u < x 0) with hAdef
    have hAne : A.Nonempty := ⟨-1, by simp [hAdef, hneg, hlt_neg]⟩
    set B : Finset ℝ := U.filter (fun u => x 0 < u) with hBdef
    have hBne : B.Nonempty := ⟨1, by simp [hBdef, hpos, hlt_pos]⟩
    have haA : A.max' hAne ∈ U := (Finset.mem_filter.mp (Finset.max'_mem A hAne)).1
    have hax : A.max' hAne < x 0 := (Finset.mem_filter.mp (Finset.max'_mem A hAne)).2
    have hbU : B.min' hBne ∈ U := (Finset.mem_filter.mp (Finset.min'_mem B hBne)).1
    have hxb : x 0 < B.min' hBne := (Finset.mem_filter.mp (Finset.min'_mem B hBne)).2
    have hconsec : ∀ u ∈ U, ¬ (A.max' hAne < u ∧ u < B.min' hBne) := by
      intro u hu
      rintro ⟨hau, hub⟩
      rcases lt_trichotomy u (x 0) with h | h | h
      · have huA : u ∈ A := Finset.mem_filter.mpr ⟨hu, h⟩
        have := Finset.le_max' A u huA
        linarith
      · exact hxU (h ▸ hu)
      · have huB : u ∈ B := Finset.mem_filter.mpr ⟨hu, h⟩
        have := Finset.min'_le B u huB
        linarith
    have hab : A.max' hAne < B.min' hBne := by linarith
    refine ⟨cellIoo (A.max' hAne) (B.min' hBne), ?_, ?_⟩
    · rw [Finset.mem_coe, mem_cuts]
      exact Or.inr ⟨A.max' hAne, haA, B.min' hBne, hbU, hab, hconsec, rfl⟩
    · rw [mem_cellIoo]; exact ⟨hax, hxb⟩

end Work.WilE7.CylAux
