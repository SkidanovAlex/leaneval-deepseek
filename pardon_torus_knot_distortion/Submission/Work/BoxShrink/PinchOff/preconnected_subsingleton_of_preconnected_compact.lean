import Mathlib
import Submission.Work.BoxShrink.PinchOff.NonCutPoint.Main

open Set

namespace Work.BoxShrink.PinchOff

/-- **A preconnected set all of whose preconnected subsets are compact is a subsingleton.**

Let `Z ⊆ ℂ` be closed and suppose that every preconnected subset of `Z` is compact.  Then every
preconnected subset `S` of `Z` is a subsingleton.  (The hypothesis is very strong: it forces `Z` to
be totally disconnected, since a nondegenerate continuum `S` would have a non-cut point `p`
(`exists_isPreconnected_compl_singleton_of_compact`), and then `S \ {p}` would be a preconnected,
non-compact subset of `Z`.) -/
theorem preconnected_subsingleton_of_preconnected_compact {Z S : Set ℂ} (hZ : IsClosed Z)
    (hcomp : ∀ C : Set ℂ, C ⊆ Z → IsPreconnected C → IsCompact C) (hSZ : S ⊆ Z)
    (hS : IsPreconnected S) : S.Subsingleton := by
  classical
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]; exact Set.subsingleton_empty
  · obtain ⟨p, hpS⟩ := h
    have hScomp : IsCompact S := hcomp S hSZ hS
    haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hScomp
    haveI : PreconnectedSpace ↥S := isPreconnected_iff_preconnectedSpace.mp hS
    haveI : Nonempty ↥S := ⟨⟨p, hpS⟩⟩
    -- a non-cut point of the continuum `S`
    obtain ⟨x, hx⟩ := exists_isPreconnected_compl_singleton_of_compact (X := ↥S) isPreconnected_univ
    -- its complement, as a subset of `ℂ`
    have himg : IsPreconnected ((Subtype.val : ↥S → ℂ) '' ({x}ᶜ : Set ↥S)) :=
      (Topology.IsInducing.isPreconnected_image (f := (Subtype.val : ↥S → ℂ))
        (Topology.IsInducing.subtypeVal (t := S))).mpr hx
    have himgsub : ((Subtype.val : ↥S → ℂ) '' ({x}ᶜ : Set ↥S)) ⊆ Z := by
      rintro y ⟨z, -, rfl⟩
      exact hSZ z.2
    -- so it must be compact, hence closed, hence `{x}` is open in `S`
    have hclosedA : IsClosed (Subtype.val ⁻¹' ((Subtype.val : ↥S → ℂ) '' ({x}ᶜ : Set ↥S))) :=
      ((hcomp _ himgsub himg).isClosed).preimage
        (show Continuous (Subtype.val : ↥S → ℂ) from continuous_subtype_val)
    have hpre : Subtype.val ⁻¹' ((Subtype.val : ↥S → ℂ) '' ({x}ᶜ : Set ↥S)) = ({x}ᶜ : Set ↥S) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, hzy⟩ hyx
        exact hz (by rw [Subtype.ext hzy, hyx])
      · intro hy
        exact ⟨y, hy, rfl⟩
    have hclosed' : IsClosed ({x}ᶜ : Set ↥S) := hpre ▸ hclosedA
    have hu : IsOpen ({x} : Set ↥S) := by simpa using hclosed'.isOpen_compl
    have hv : IsOpen ({x}ᶜ : Set ↥S) := isClosed_singleton.isOpen_compl
    have hcov : (univ : Set ↥S) ⊆ ({x} : Set ↥S) ∪ ({x}ᶜ : Set ↥S) := by
      rw [union_compl_self]
    rcases isPreconnected_univ.subset_or_subset hu hv disjoint_compl_right hcov with h1 | h1
    · -- `↥S` is a singleton
      have hsub : S ⊆ {x.1} := by
        intro y hy
        have hy' : (⟨y, hy⟩ : ↥S) = x := by simpa using h1 (mem_univ _)
        simpa using congrArg Subtype.val hy'
      exact fun a ha b hb => by rw [hsub ha, hsub hb]
    · exact absurd (h1 (mem_univ x)) (by simp)

end Work.BoxShrink.PinchOff
