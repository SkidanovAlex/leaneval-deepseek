import Mathlib
import Submission.Work.WilC4aA.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter Set
namespace Work.WilC4aA

open WilkiesDesign WilkiesDesign.CG WilkiesDesign.CG.C4a

/-- The negation of `Accum P`, unfolded: some positive `δ` bounds the piece `P` away from the
`t`-axis; no point of `P.set` has its `t`-coordinate in `(0, δ)`. -/
theorem exists_delta_of_not_accum_single (P : LiftPiece) (h : ¬ Accum P) :
    ∃ δ > (0 : ℝ), ∀ z ∈ P.set, z 0 ∉ Set.Ioo (0 : ℝ) δ := by
  by_contra hc
  apply h
  intro δ hδ
  by_contra hx
  exact hc ⟨δ, hδ, fun z hz hmem => hx ⟨z, hz, hmem⟩⟩

/-- A finite union of pieces, none of which accumulates at the `t`-axis, stays away from the axis:
the pointwise bounds may be intersected by taking the minimum over the (finite) list. -/
theorem exists_delta_of_not_accum (L : List WilkiesDesign.CG.C4a.LiftPiece)
    (h : ∀ P ∈ L, ¬ Work.WilC4aA.Accum P) :
    ∃ δ > (0 : ℝ), ∀ P ∈ L, ∀ z ∈ P.set, z 0 ∉ Set.Ioo (0 : ℝ) δ := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons P L ih =>
    have hP : ¬ Accum P := h P (by simp)
    have hL : ∀ Q ∈ L, ¬ Accum Q := fun Q hQ => h Q (List.mem_cons_of_mem P hQ)
    obtain ⟨δ₁, hδ₁, h₁⟩ := exists_delta_of_not_accum_single P hP
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih hL
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro Q hQ z hz
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact fun hmem => h₁ z hz ⟨hmem.1, lt_of_lt_of_le hmem.2 (min_le_left δ₁ δ₂)⟩
    · exact fun hmem => h₂ Q hQ z hz ⟨hmem.1, lt_of_lt_of_le hmem.2 (min_le_right δ₁ δ₂)⟩

end Work.WilC4aA
