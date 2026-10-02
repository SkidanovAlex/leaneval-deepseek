/-
# The image of the four-arc parametrisation is the union of the four arcs

The concatenation `fourArcs γ₁ γ₂ γ₃ γ₄ : ℝ → ℂ` runs through `γ₁` on `[0,1/4]`, `γ₂` on
`[1/4,1/2]`, `γ₃` on `[1/2,3/4]` and `γ₄` on `[3/4,1]`.  This file records the elementary but
slightly fiddly consequence that its image on the fundamental interval `[0,1)` is exactly the
union of the images of the four arcs.

The hypotheses `γ₁ 1 = γ₂ 0`, … are needed at the *junctions*: the point where two consecutive
arcs meet belongs to both arcs (e.g. `γ₂ 0 = γ₁ 1`), so that the half-open interval `[0,1)` —
which excludes the endpoint `1` — still covers all four arcs completely.
-/
import Mathlib
import Submission.Work.Top.FourArcsDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set
open scoped Topology

namespace Work.Top

/-- The image of `[0,1]` under the four-arc concatenation is the union of the four arcs. -/
theorem fourArcs_image_Icc (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ))
    (h₁₂ : γ₁ 1 = γ₂ 0) (h₂₃ : γ₂ 1 = γ₃ 0) (h₃₄ : γ₃ 1 = γ₄ 0) :
    fourArcs γ₁ γ₂ γ₃ γ₄ '' Set.Icc (0:ℝ) 1
      = Set.range γ₁ ∪ Set.range γ₂ ∪ Set.range γ₃ ∪ Set.range γ₄ := by
  apply Set.Subset.antisymm
  · -- Every point of the image lies in the range of one of the four arcs.
    rintro z ⟨t, ht, rfl⟩
    rw [Set.mem_Icc] at ht
    rcases le_or_gt t (1/4) with h | h
    · rw [fourArcs_eq_arcPt₁ _ _ _ _ h]
      exact Or.inl (Or.inl (Or.inl (arcPt_mem_range γ₁ _)))
    · rcases le_or_gt t (1/2) with h2 | h2
      · rw [fourArcs_eq_arcPt₂ _ _ _ _ h h2]
        exact Or.inl (Or.inl (Or.inr (arcPt_mem_range γ₂ _)))
      · rcases le_or_gt t (3/4) with h3 | h3
        · rw [fourArcs_eq_arcPt₃ _ _ _ _ h2 h3]
          exact Or.inl (Or.inr (arcPt_mem_range γ₃ _))
        · rw [fourArcs_eq_arcPt₄ _ _ _ _ h3]
          exact Or.inr (arcPt_mem_range γ₄ _)
  · -- Conversely each arc is traced out on `[0,1]`; at the junctions we use the matching of
    -- consecutive endpoints.
    intro z hz
    rw [Set.mem_union, Set.mem_union, Set.mem_union] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · rcases hz with ⟨s, rfl⟩
      refine ⟨(s:ℝ)/4, ⟨by linarith [s.2.1], by linarith [s.2.2]⟩, ?_⟩
      rw [fourArcs_eq_arcPt₁ _ _ _ _ (by linarith [s.2.2]),
        show (4:ℝ)*((s:ℝ)/4) = (s:ℝ) by ring, arcPt_of_mem γ₁ s.2]
    · rcases hz with ⟨s, rfl⟩
      rcases eq_or_ne (s:ℝ) 0 with hs | hs
      · -- `γ₂ 0 = γ₁ 1`: the junction with the first arc.
        have hs0 : s = (0 : unitInterval) := Subtype.ext hs
        refine ⟨1/4, ⟨by norm_num, by norm_num⟩, ?_⟩
        rw [fourArcs_eq_arcPt₁ _ _ _ _ (le_refl _),
          show (4:ℝ)*(1/4) = 1 by norm_num, arcPt_one, hs0]
        exact h₁₂
      · refine ⟨((s:ℝ)+1)/4, ⟨by linarith [s.2.1], by linarith [s.2.2]⟩, ?_⟩
        rw [fourArcs_eq_arcPt₂ _ _ _ _
              (by have : 0 < (s:ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs); linarith)
              (by linarith [s.2.2]),
          show (4:ℝ)*(((s:ℝ)+1)/4) - 1 = (s:ℝ) by ring, arcPt_of_mem γ₂ s.2]
    · rcases hz with ⟨s, rfl⟩
      rcases eq_or_ne (s:ℝ) 0 with hs | hs
      · -- `γ₃ 0 = γ₂ 1`: the junction with the second arc.
        have hs0 : s = (0 : unitInterval) := Subtype.ext hs
        refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
        rw [fourArcs_eq_arcPt₂ _ _ _ _ (by norm_num) (le_refl _),
          show (4:ℝ)*(1/2) - 1 = 1 by norm_num, arcPt_one, hs0]
        exact h₂₃
      · refine ⟨((s:ℝ)+2)/4, ⟨by linarith [s.2.1], by linarith [s.2.2]⟩, ?_⟩
        rw [fourArcs_eq_arcPt₃ _ _ _ _
              (by have : 0 < (s:ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs); linarith)
              (by linarith [s.2.2]),
          show (4:ℝ)*(((s:ℝ)+2)/4) - 2 = (s:ℝ) by ring, arcPt_of_mem γ₃ s.2]
    · rcases hz with ⟨s, rfl⟩
      rcases eq_or_ne (s:ℝ) 0 with hs | hs
      · -- `γ₄ 0 = γ₃ 1`: the junction with the third arc.
        have hs0 : s = (0 : unitInterval) := Subtype.ext hs
        refine ⟨3/4, ⟨by norm_num, by norm_num⟩, ?_⟩
        rw [fourArcs_eq_arcPt₃ _ _ _ _ (by norm_num) (le_refl _),
          show (4:ℝ)*(3/4) - 2 = 1 by norm_num, arcPt_one, hs0]
        exact h₃₄
      · refine ⟨((s:ℝ)+3)/4, ⟨by linarith [s.2.1], by linarith [s.2.2]⟩, ?_⟩
        rw [fourArcs_eq_arcPt₄ _ _ _ _
              (by have : 0 < (s:ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs); linarith),
          show (4:ℝ)*(((s:ℝ)+3)/4) - 3 = (s:ℝ) by ring, arcPt_of_mem γ₄ s.2]

/-- The image of `[0,1]` and the image of the half-open `[0,1)` agree, because the extra
endpoint `1` is already hit at `0` (`γ₄ 1 = γ₁ 0`). -/
theorem fourArcs_image_Icc_eq_image_Ico (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ))
    (h₄₁ : γ₄ 1 = γ₁ 0) :
    fourArcs γ₁ γ₂ γ₃ γ₄ '' Set.Ico (0:ℝ) 1
      = fourArcs γ₁ γ₂ γ₃ γ₄ '' Set.Icc (0:ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.image_mono (fun x hx => ⟨hx.1, le_of_lt hx.2⟩)
  · rintro z ⟨t, ht, htz⟩
    rw [Set.mem_Icc] at ht
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact ⟨t, ⟨ht.1, h⟩, htz⟩
    · subst h
      refine ⟨0, ⟨le_refl 0, by norm_num⟩, ?_⟩
      rw [fourArcs_zero, ← htz, fourArcs_one]
      exact h₄₁.symm

/-- The image of the half-open fundamental interval `[0,1)` under the four-arc concatenation is
the union of the images of the four arcs. -/
theorem fourArcs_image_Ico (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ))
    (h₁₂ : γ₁ 1 = γ₂ 0) (h₂₃ : γ₂ 1 = γ₃ 0) (h₃₄ : γ₃ 1 = γ₄ 0) (h₄₁ : γ₄ 1 = γ₁ 0) :
    fourArcs γ₁ γ₂ γ₃ γ₄ '' Set.Ico (0:ℝ) 1
      = Set.range γ₁ ∪ Set.range γ₂ ∪ Set.range γ₃ ∪ Set.range γ₄ := by
  rw [fourArcs_image_Icc_eq_image_Ico γ₁ γ₂ γ₃ γ₄ h₄₁,
    fourArcs_image_Icc γ₁ γ₂ γ₃ γ₄ h₁₂ h₂₃ h₃₄]

end Work.Top
