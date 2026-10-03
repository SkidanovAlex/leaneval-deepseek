import Mathlib

namespace Work.Section3.RkFinModel

universe u

/-- Replacing the generator `u` by `u - E u` does not change the submodule
`range E ⊔ span {u}`: the difference `E u` lies in `range E`, so
`u = (u - E u) + E u` exhibits `u` in the right-hand side while
`u - E u = u - E u` exhibits the new generator in the left-hand side. -/
theorem rkcs_range_sup_span_eq_range_sup_span_sub_proj {S : Type u} [Ring S] {n : ℕ}
    (E : Module.End S (Fin n → S)) (u : Fin n → S) :
    LinearMap.range E ⊔ Submodule.span S ({u} : Set (Fin n → S))
      = LinearMap.range E ⊔ Submodule.span S ({u - E u} : Set (Fin n → S)) := by
  refine le_antisymm ?_ ?_
  · rw [sup_le_iff]
    refine ⟨le_sup_left, ?_⟩
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.mem_sup.mpr
      ⟨E u, LinearMap.mem_range_self E u, u - E u,
        Submodule.subset_span (Set.mem_singleton _),
        by rw [add_comm]; exact sub_add_cancel u (E u)⟩
  · rw [sup_le_iff]
    refine ⟨le_sup_left, ?_⟩
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.mem_sup.mpr
      ⟨-E u, neg_mem (LinearMap.mem_range_self E u), u,
        Submodule.subset_span (Set.mem_singleton _),
        by rw [sub_eq_add_neg, add_comm]⟩

end Work.Section3.RkFinModel
