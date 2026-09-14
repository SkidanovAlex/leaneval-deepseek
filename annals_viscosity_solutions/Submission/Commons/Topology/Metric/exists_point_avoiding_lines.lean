import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.Topology.Metric

open Set
open scoped Pointwise

/-- A point on the line through `p` in direction `v` lies in `p +ᵥ ℝ∙v`. -/
private lemma vadd_span_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p v : E) (t : ℝ) : p + t • v ∈ p +ᵥ (Submodule.span ℝ {v} : Set E) := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  simpa [add_sub_cancel_left] using
    Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)

/-- The translate of the line spanned by a nonzero vector is closed. -/
private lemma isClosed_vadd_span_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p v : E) :
    IsClosed (p +ᵥ (Submodule.span ℝ {v} : Set E)) :=
  (Submodule.closed_of_finiteDimensional (Submodule.span ℝ {v})).vadd p

/-- In a space of dimension at least two, the translate of the line spanned by a nonzero vector
has empty interior. -/
private lemma interior_vadd_span_singleton_eq_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E) (p : E) {v : E} (hv : v ≠ 0) :
    interior (p +ᵥ (Submodule.span ℝ {v} : Set E)) = ∅ := by
  have hS : interior ((Submodule.span ℝ {v} : Submodule ℝ E) : Set E) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have htop : Submodule.span ℝ {v} = ⊤ :=
      Submodule.eq_top_of_nonempty_interior' _ ⟨x, hx⟩
    have hfr : Module.finrank ℝ E = 1 := by
      rw [← finrank_top ℝ E, ← htop]
      exact finrank_span_singleton hv
    omega
  rw [interior_vadd, hS]
  simp

/-- Given a finite set `F` of points of a real inner product space `E` of dimension at least two,
and two points `p, q ∉ F`, there exists a point `c` which is not in `F`, lies on no line through
`p` and a point of `F`, and lies on no line through `q` and a point of `F`.

The bad set (the union of `F`, of the finitely many lines through `p` and through points of `F`,
and of the finitely many lines through `q` and through points of `F`) is a finite union of proper
affine subspaces, hence has empty interior. -/
theorem exists_point_avoiding_lines
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E) (F : Finset E) (p q : E) (hp : p ∉ F) (hq : q ∉ F) :
    ∃ c : E, c ∉ F ∧
      (∀ f ∈ F, ∀ t : ℝ, c ≠ p + t • (f - p)) ∧
      (∀ f ∈ F, ∀ t : ℝ, c ≠ q + t • (f - q)) := by
  classical
  -- The bad set is the union of the lines through `p` and `q` in the directions of the points of
  -- `F`, indexed by `F ⊕ F` (left = lines through `p`, right = lines through `q`).
  let g : F ⊕ F → Set E := Sum.elim
    (fun f => p +ᵥ ((Submodule.span ℝ {((f : E) - p)}) : Set E))
    (fun f => q +ᵥ ((Submodule.span ℝ {((f : E) - q)}) : Set E))
  have hclosed : ∀ i, IsClosed (g i) := by
    intro i
    cases i with
    | inl f => simpa only [g, Sum.elim_inl] using
        isClosed_vadd_span_singleton (E := E) p ((f : E) - p)
    | inr f => simpa only [g, Sum.elim_inr] using
        isClosed_vadd_span_singleton (E := E) q ((f : E) - q)
  have hnonzero_l : ∀ f : F, ((f : E) - p) ≠ 0 :=
    fun f => sub_ne_zero.mpr (fun h => hp (h ▸ f.2))
  have hnonzero_r : ∀ f : F, ((f : E) - q) ≠ 0 :=
    fun f => sub_ne_zero.mpr (fun h => hq (h ▸ f.2))
  have hemp : ∀ i, interior (g i) = ∅ := by
    intro i
    cases i with
    | inl f => simpa only [g, Sum.elim_inl] using
        interior_vadd_span_singleton_eq_empty hdim p (hnonzero_l f)
    | inr f => simpa only [g, Sum.elim_inr] using
        interior_vadd_span_singleton_eq_empty hdim q (hnonzero_r f)
  -- By Baire's theorem the bad set does not cover the whole space.
  have hcover : ⋃ i, g i ≠ univ := by
    intro hcov
    obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcov
    rw [hemp i] at hi
    exact Set.not_nonempty_empty hi
  obtain ⟨c, hc⟩ : ∃ c, c ∉ ⋃ i, g i := by
    by_contra h
    apply hcover
    rw [Set.eq_univ_iff_forall]
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hmem_l : ∀ (f : F) (t : ℝ), p + t • ((f : E) - p) ∈ g (Sum.inl f) :=
    fun f t => vadd_span_mem p ((f : E) - p) t
  have hmem_r : ∀ (f : F) (t : ℝ), q + t • ((f : E) - q) ∈ g (Sum.inr f) :=
    fun f t => vadd_span_mem q ((f : E) - q) t
  refine ⟨c, ?_, ?_, ?_⟩
  · -- `c ∉ F`: a point of `F` lies on the line through `p` in its own direction.
    intro hcF
    have : c ∈ g (Sum.inl (⟨c, hcF⟩ : F)) := by
      simpa only [one_smul, add_sub_cancel] using hmem_l ⟨c, hcF⟩ 1
    exact hc (Set.mem_iUnion.mpr ⟨_, this⟩)
  · intro f hf t ht
    have : c ∈ g (Sum.inl (⟨f, hf⟩ : F)) := by
      rw [ht]; exact hmem_l ⟨f, hf⟩ t
    exact hc (Set.mem_iUnion.mpr ⟨_, this⟩)
  · intro f hf t ht
    have : c ∈ g (Sum.inr (⟨f, hf⟩ : F)) := by
      rw [ht]; exact hmem_r ⟨f, hf⟩ t
    exact hc (Set.mem_iUnion.mpr ⟨_, this⟩)

end Commons.Topology.Metric