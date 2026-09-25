import Mathlib

namespace Work.CFTLib.Algebra

/-- **A module all of whose finitely generated submodules have bounded `finrank` is finite
dimensional, with the same bound.**

If every finitely generated `K`-submodule `W ≤ V` satisfies `Module.finrank K W ≤ N`, then `V` is
finite dimensional and `Module.finrank K V ≤ N`.

Indeed, if `V` were infinite dimensional then (over a field) it would contain `N+1` linearly
independent elements; their span is a finitely generated submodule of `finrank N+1 > N`,
contradiction.  Conversely if `V` is finite dimensional then `⊤` is finitely generated, so
`Module.finrank K V = Module.finrank K ⊤ ≤ N`.

This is the standard criterion used to deduce finite dimensionality of a filtered colimit from a
uniform bound on the dimensions of the images of the finite levels. -/
theorem finiteDimensional_of_bdd_finrank
    (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (N : ℕ)
    (h : ∀ (W : Submodule K V), W.FG → Module.finrank K W ≤ N) :
    FiniteDimensional K V ∧ Module.finrank K V ≤ N := by
  -- A finitely many element linearly independent set spans a finitely generated submodule, whose
  -- `finrank` is therefore bounded by `N`; this bounds the cardinality of the set.
  have H : ∀ s : Finset V, (LinearIndependent K fun i : s => (i : V)) → s.card ≤ N := by
    intro s hs
    have hFG : (Submodule.span K (s : Set V)).FG := Submodule.fg_span s.finite_toSet
    have hle : Module.finrank K (Submodule.span K (s : Set V)) ≤ N := h _ hFG
    have heq : Module.finrank K (Submodule.span K (s : Set V)) = s.card := by
      rw [show (s : Set V) = Set.range (fun i : s => (i : V)) from (Subtype.range_coe).symm]
      rw [finrank_span_eq_card hs]
      exact Fintype.card_coe s
    omega
  -- Hence the rank of `V` is at most `N`, in particular finite.
  have hrank : Module.rank K V ≤ (N : Cardinal) := rank_le H
  have hlt : Module.rank K V < Cardinal.aleph0 := lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0
  have hfin : Module.Finite K V := Module.rank_lt_aleph0_iff.mp hlt
  refine ⟨hfin, ?_⟩
  -- And the `finrank` coincides with the (finite) rank.
  have h1 : (Module.finrank K V : Cardinal) ≤ (N : Cardinal) := by
    rw [Module.finrank_eq_rank]
    exact hrank
  exact Nat.cast_le.mp h1

end Work.CFTLib.Algebra
