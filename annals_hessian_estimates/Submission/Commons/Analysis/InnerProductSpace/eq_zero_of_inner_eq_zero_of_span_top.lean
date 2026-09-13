import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace Commons.Analysis.InnerProductSpace

lemma eq_zero_of_inner_eq_zero_of_span_top {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) (s : Set E)
    (hx : ∀ y ∈ s, inner ℝ x y = 0) (hspan : Submodule.span ℝ s = ⊤) : x = 0 := by
  have hxorth : x ∈ (Submodule.span ℝ s)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    refine Submodule.span_induction (s := s) (p := fun z _ => inner ℝ z x = 0) ?mem ?zero ?add ?smul hy
    · intro z hz
      exact (inner_eq_zero_symm.mp (hx z hz))
    · simp
    · intro a b ha hb ih1 ih2
      rw [inner_add_left]
      simp [ih1, ih2]
    · intro a z hz ih
      rw [inner_smul_left]
      simp [ih]
  have hmem : x ∈ (Submodule.span ℝ s) := by
    rw [hspan]
    trivial
  have hxx : inner ℝ x x = 0 :=
    (Submodule.mem_orthogonal (Submodule.span ℝ s) x).mp hxorth x hmem
  exact inner_self_eq_zero.mp hxx

end Commons.Analysis.InnerProductSpace