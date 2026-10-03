/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Geodesics in a tree

Between any two vertices of a tree there is an injective walk (a geodesic), enumerated as
`x 0, x 1, …, x d`.  This is the combinatorial input for the subdivision of the source complex
of the Dunwoody construction (`RESOLUTION_PLAN_2.md`, obligation (O5)): the source edge
`(g, i, ε)` of the Cayley complex is subdivided at the preimages of the midpoints of the edges
of `T` traversed by the geodesic from `g • t₀` to `g * x i ^ ε • t₀`, so that each sub-edge maps
to a *single* edge of the barycentric subdivision `T'` (or to a point).
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

open SimpleGraph

/-- **Geodesics in a tree, enumerated.**  Every two vertices of a tree are joined by an
injective walk, i.e. by a geodesic: vertices `x 0, x 1, …, x d`, pairwise distinct, with
`x 0 = u`, `x d = v` and consecutive vertices adjacent.

(`d` is the graph distance, see `SimpleGraph.Walk.length_eq_dist`, but the statement below only
needs the enumeration.) -/
theorem exists_geodesic {V : Type u} (T : SimpleGraph V) (hT : T.IsTree) (u v : V) :
    ∃ (d : ℕ) (x : Fin (d + 1) → V),
      x 0 = u ∧ x (Fin.last d) = v ∧
      (∀ i : Fin d, T.Adj (x i.castSucc) (x i.succ)) ∧ Function.Injective x := by
  obtain ⟨p, hp, -⟩ := hT.existsUnique_path u v
  refine ⟨p.length, fun i => p.getVert (i : ℕ), p.getVert_zero, p.getVert_length, ?_, ?_⟩
  · intro i
    exact p.adj_getVert_succ i.isLt
  · intro i j hij
    have hi : (i : ℕ) ≤ p.length := Nat.lt_succ_iff.mp i.isLt
    have hj : (j : ℕ) ≤ p.length := Nat.lt_succ_iff.mp j.isLt
    have h : (i : ℕ) = (j : ℕ) := hp.getVert_injOn hi hj hij
    exact Fin.ext h

end Work.ORDunwoody
