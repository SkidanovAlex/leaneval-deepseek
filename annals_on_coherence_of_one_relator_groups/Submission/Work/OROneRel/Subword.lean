/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).
-/
import Submission.Work.OROneRel.Basic

/-!
# The subword relation on free groups

`IsSubwordOf v r` says that the reduced word of `v` occurs as a contiguous block of the reduced word
of `r`.  Here we record the elementary API: reflexivity, transitivity, monotonicity of the length and
of the set of letters.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

theorem isSubwordOf_refl (r : FreeGroup α) : IsSubwordOf r r := by
  classical
  refine ⟨[], [], ?_⟩
  simp

theorem isSubwordOf_trans {u v r : FreeGroup α} (h₁ : IsSubwordOf u v) (h₂ : IsSubwordOf v r) :
    IsSubwordOf u r := by
  classical
  obtain ⟨A, B, hAB⟩ := h₁
  obtain ⟨C, D, hCD⟩ := h₂
  refine ⟨C ++ A, B ++ D, ?_⟩
  simp only [hCD, hAB, List.append_assoc]

theorem relatorNorm_le_of_isSubwordOf {v r : FreeGroup α} (h : IsSubwordOf v r) :
    relatorNorm v ≤ relatorNorm r := by
  classical
  obtain ⟨L₁, L₂, hL⟩ := h
  simp only [relatorNorm, FreeGroup.norm, hL, List.length_append]
  omega

theorem relatorLetters_subset_of_isSubwordOf {v r : FreeGroup α} (h : IsSubwordOf v r) :
    relatorLetters v ⊆ relatorLetters r := by
  classical
  obtain ⟨L₁, L₂, hL⟩ := h
  intro a ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  rw [hL, List.mem_append]
  exact Or.inl (List.mem_append.mpr (Or.inr hb))

end Work.OROneRel
