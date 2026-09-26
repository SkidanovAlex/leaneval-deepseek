import Mathlib

namespace Work.BoxShrink.Bubble.Plane

open Set Filter
open scoped Pointwise Topology

/-- The line in the plane `ℝ × ℝ` spanned by a single vector, as a set. -/
def lineSpan (c : ℝ × ℝ) : Set (ℝ × ℝ) := Submodule.span ℝ ({c} : Set (ℝ × ℝ))

@[simp] lemma mem_lineSpan (c z : ℝ × ℝ) :
    z ∈ lineSpan c ↔ z ∈ Submodule.span ℝ ({c} : Set (ℝ × ℝ)) := Iff.rfl

/-- In the plane `ℝ × ℝ`, the line spanned by a single vector is a proper subspace:
it has dimension at most one while the ambient space has dimension two. -/
lemma span_singleton_ne_top (c : ℝ × ℝ) :
    Submodule.span ℝ ({c} : Set (ℝ × ℝ)) ≠ (⊤ : Submodule ℝ (ℝ × ℝ)) := by
  have hlt : Submodule.span ℝ ({c} : Set (ℝ × ℝ)) < (⊤ : Submodule ℝ (ℝ × ℝ)) := by
    apply span_lt_top_of_card_lt_finrank
    rw [Module.finrank_prod, Module.finrank_self]
    simp
  exact ne_of_lt hlt

/-- A proper submodule of the plane has empty interior (a submodule with nonempty
interior is everything). -/
lemma interior_lineSpan (c : ℝ × ℝ) : interior (lineSpan c) = ∅ := by
  by_contra h
  exact span_singleton_ne_top c
    (Submodule.eq_top_of_nonempty_interior' _
      (Set.nonempty_iff_ne_empty.mpr h))

/-- The segment from `a` to `b` is contained in the translate by `a` of the line
spanned by `b - a`. -/
lemma segment_subset_vadd_lineSpan (a b : ℝ × ℝ) : segment ℝ a b ⊆ a +ᵥ lineSpan (b - a) := by
  rw [segment_eq_image_lineMap]
  rintro x ⟨t, -, rfl⟩
  refine ⟨t • (b - a), Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton _)), ?_⟩
  simp only [AffineMap.lineMap_apply_module', vadd_eq_add, add_comm]

theorem segment_interior_eq_empty (a b : ℝ × ℝ) : interior (segment ℝ a b) = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  calc interior (segment ℝ a b)
      ⊆ interior (a +ᵥ lineSpan (b - a)) := interior_mono (segment_subset_vadd_lineSpan a b)
    _ = a +ᵥ interior (lineSpan (b - a)) := interior_vadd a _
    _ = a +ᵥ (∅ : Set (ℝ × ℝ)) := by rw [interior_lineSpan]
    _ = ∅ := by simp

end Work.BoxShrink.Bubble.Plane
