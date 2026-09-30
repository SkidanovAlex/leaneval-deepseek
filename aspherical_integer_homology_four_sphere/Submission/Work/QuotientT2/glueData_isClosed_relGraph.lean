import Mathlib
import Submission.Work.QuotientT2.Adjunction
import Submission.Work.QuotientT2.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Topology Function

namespace Work.QuotientT2

theorem glueData_isClosed_relGraph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] (G : GlueData X Y) : IsClosed (relGraph G.setoid) := by
  have hA : IsClosed {p : X × Y | ∃ hx : p.1 ∈ G.s, ((G.h ⟨p.1, hx⟩ : G.t) : Y) = p.2} :=
    isClosed_graph_of_continuous G.s_closed (fun x : G.s => ((G.h x : G.t) : Y))
      (continuous_subtype_val.comp G.h.continuous)
  have hB : IsClosed {p : Y × X | ∃ hy : p.1 ∈ G.t, ((G.h.symm ⟨p.1, hy⟩ : G.s) : X) = p.2} :=
    isClosed_graph_of_continuous G.t_closed (fun y : G.t => ((G.h.symm y : G.s) : X))
      (continuous_subtype_val.comp G.h.symm.continuous)
  have hS1 : (Prod.map (Sum.inl : X → X ⊕ Y) (Sum.inr : Y → X ⊕ Y)) ''
        {p : X × Y | ∃ hx : p.1 ∈ G.s, ((G.h ⟨p.1, hx⟩ : G.t) : Y) = p.2}
      = {p : (X ⊕ Y) × (X ⊕ Y) | ∃ x : G.s, p.1 = Sum.inl (x : X) ∧
          p.2 = Sum.inr ((G.h x : G.t) : Y)} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hx, hval⟩ := hq
      refine ⟨⟨q.1, hx⟩, ?_, ?_⟩
      · rfl
      · show Sum.inr q.2 = Sum.inr ((G.h ⟨q.1, hx⟩ : G.t) : Y)
        rw [hval]
    · rintro ⟨x, h1, h2⟩
      refine ⟨(x.1, ((G.h x : G.t) : Y)), ⟨x.2, rfl⟩, ?_⟩
      exact Prod.ext h1.symm h2.symm
  have hS2 : (Prod.map (Sum.inr : Y → X ⊕ Y) (Sum.inl : X → X ⊕ Y)) ''
        {p : Y × X | ∃ hy : p.1 ∈ G.t, ((G.h.symm ⟨p.1, hy⟩ : G.s) : X) = p.2}
      = {p : (X ⊕ Y) × (X ⊕ Y) | ∃ y : G.t, p.1 = Sum.inr (y : Y) ∧
          p.2 = Sum.inl ((G.h.symm y : G.s) : X)} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hy, hval⟩ := hq
      refine ⟨⟨q.1, hy⟩, ?_, ?_⟩
      · rfl
      · show Sum.inl q.2 = Sum.inl ((G.h.symm ⟨q.1, hy⟩ : G.s) : X)
        rw [hval]
    · rintro ⟨y, h1, h2⟩
      refine ⟨(y.1, ((G.h.symm y : G.s) : X)), ⟨y.2, rfl⟩, ?_⟩
      exact Prod.ext h1.symm h2.symm
  have h1 : IsClosed {p : (X ⊕ Y) × (X ⊕ Y) | ∃ x : G.s, p.1 = Sum.inl (x : X) ∧
        p.2 = Sum.inr ((G.h x : G.t) : Y)} := by
    rw [← hS1]
    exact (IsClosedEmbedding.inl.prodMap IsClosedEmbedding.inr).isClosed_iff_image_isClosed.mp hA
  have h2 : IsClosed {p : (X ⊕ Y) × (X ⊕ Y) | ∃ y : G.t, p.1 = Sum.inr (y : Y) ∧
        p.2 = Sum.inl ((G.h.symm y : G.s) : X)} := by
    rw [← hS2]
    exact (IsClosedEmbedding.inr.prodMap IsClosedEmbedding.inl).isClosed_iff_image_isClosed.mp hB
  have h3 : IsClosed (Set.diagonal (X ⊕ Y)) := isClosed_diagonal
  have hgraph : relGraph G.setoid =
      ({p : (X ⊕ Y) × (X ⊕ Y) | ∃ x : G.s, p.1 = Sum.inl (x : X) ∧
          p.2 = Sum.inr ((G.h x : G.t) : Y)} ∪
        ({p : (X ⊕ Y) × (X ⊕ Y) | ∃ y : G.t, p.1 = Sum.inr (y : Y) ∧
          p.2 = Sum.inl ((G.h.symm y : G.s) : X)} ∪ Set.diagonal (X ⊕ Y))) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [mem_relGraph, Set.mem_setOf_eq, Set.mem_union, Set.mem_diagonal_iff]
    exact G.rel_iff a b
  rw [hgraph]
  exact h1.union (h2.union h3)

end Work.QuotientT2
