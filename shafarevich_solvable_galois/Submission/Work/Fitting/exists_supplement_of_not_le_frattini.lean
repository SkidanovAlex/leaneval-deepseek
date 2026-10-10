import Mathlib.GroupTheory.Frattini
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Supplements of a normal subgroup outside the Frattini subgroup

If `N ◁ G` is not contained in the Frattini subgroup `Φ(G) = frattini G` (the intersection of
the maximal subgroups of `G`), then `N` admits a *proper* supplement: there is `U < G` with
`N ⊔ U = ⊤`.

The proof is one line of lattice theory.  Since `Φ(G) = ⨅ {K | IsCoatom K}` and `N ≰ Φ(G)`,
there is a maximal subgroup `K < G` with `N ≰ K`; maximality then forces `N ⊔ K = ⊤`.

This is the group-theoretic input used in the Ore/Shafarevich reduction: applied to `N = F(G)`
(a nontrivial finite solvable group has `F(G) ≰ Φ(G)`) it produces the proper subgroup `U` on
which the induction on `Nat.card G` runs.
-/

namespace Work.Fitting

open Subgroup

variable {G : Type*} [Group G]

/-- A subgroup not contained in the Frattini subgroup is not contained in some maximal
subgroup (a coatom of the subgroup lattice). -/
theorem exists_coatom_not_le_frattini (N : Subgroup G) (h : ¬ N ≤ frattini G) :
    ∃ K : Subgroup G, IsCoatom K ∧ ¬ N ≤ K := by
  rw [frattini, Order.radical, le_iInf₂_iff] at h
  simp only [Set.mem_ofPred_eq, not_forall] at h
  obtain ⟨K, hKc, hKn⟩ := h
  exact ⟨K, hKc, hKn⟩

/-- **Supplement lemma.**  A normal subgroup `N ◁ G` with `N ≰ Φ(G)` has a proper supplement:
there is a proper subgroup `U ≠ ⊤` with `N ⊔ U = ⊤`. -/
theorem exists_supplement_of_not_le_frattini {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (h : ¬ N ≤ frattini G) :
    ∃ U : Subgroup G, U ≠ ⊤ ∧ N ⊔ U = ⊤ := by
  obtain ⟨K, hKc, hKn⟩ := exists_coatom_not_le_frattini N h
  refine ⟨K, hKc.1, ?_⟩
  have hlt : K < N ⊔ K := by
    rw [lt_iff_le_and_ne]
    exact ⟨le_sup_right, fun heq => hKn (heq ▸ le_sup_left)⟩
  exact hKc.lt_iff.mp hlt

end Work.Fitting
