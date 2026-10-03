import Mathlib

namespace Work.BasinSC.Tower

/-- The connected component of `x` in `F` is a connected component of `F` in the topological
sense: it is closed in the subspace `F`, which is expressed here as
`connectedComponentIn F x = F ∩ closure (connectedComponentIn F x)`.

The proof is the elementary maximality argument.  Let `C := connectedComponentIn F x`.

* `C ⊆ F` by definition and `C ⊆ closure C` always, giving `C ⊆ F ∩ closure C`.

* Conversely, if `x ∈ F` then `C` contains `x`; `C ⊆ F ∩ closure C ⊆ closure C` and
  `F ∩ closure C ⊆ closure C = closure C`, so by `IsPreconnected.subset_closure`
  the set `F ∩ closure C` is preconnected (it lies between the preconnected set `C` and its
  closure).  It contains `x` and is contained in `F`, hence by maximality of the component
  (`IsPreconnected.subset_connectedComponentIn`) it is a subset of `C`.

If `x ∉ F` both sides are empty. -/
lemma connectedComponentIn_inter_closure {α : Type*} [TopologicalSpace α] {F : Set α} {x : α} :
    connectedComponentIn F x = F ∩ closure (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine subset_antisymm ?_ ?_
    · rintro y hy
      exact ⟨connectedComponentIn_subset F x hy, subset_closure hy⟩
    · have hpre : IsPreconnected (F ∩ closure (connectedComponentIn F x)) :=
        IsPreconnected.subset_closure (s := connectedComponentIn F x)
          isPreconnected_connectedComponentIn
          (fun z hz => ⟨connectedComponentIn_subset F x hz, subset_closure hz⟩)
          Set.inter_subset_right
      exact hpre.subset_connectedComponentIn
        ⟨hx, subset_closure (mem_connectedComponentIn hx)⟩ Set.inter_subset_left
  · simp [connectedComponentIn_eq_empty hx]

end Work.BasinSC.Tower
