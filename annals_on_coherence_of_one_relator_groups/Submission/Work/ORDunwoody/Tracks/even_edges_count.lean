/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# A closed walk in a forest crosses every edge an even number of times

`Work.ORDunwoody.Tracks.even_edges_count`: if `T` is acyclic (a forest) and `w : T.Walk u u` is a
closed walk, then for **every** unordered pair `e : Sym2 V` (whether or not it is an edge of `T`)
the number of times `w` traverses `e` is even.

This is the elementary input for the "colour lemma"/level-set construction of Dunwoody's
resolution (`RESOLUTION_PLAN_2.md`, fact 4: the boundary walk of a polygon maps to a closed walk
in the subdivided tree `T'`, which must therefore cross each edge of `T'` evenly).

The proof is the classical cut argument.  For a genuine edge `e = s(x, y)` of `T`, acyclicity
says (`isAcyclic_iff_forall_adj_isBridge`) that `e` is a bridge, i.e. `x` and `y` are no longer
reachable from one another in `T.deleteEdges {e}`.  Hence the vertex predicate

  `side z := (T.deleteEdges {e}).Reachable x z`

separates exactly the two sides of the bridge: for *adjacent* `p, q` one has `side p ≠ side q`
iff the traversed edge `s(p, q)` **is** the bridge `e` (`cut` below — the only place acyclicity is
used).  So along a walk the parity of the number of traversals of `e` flips exactly when the walk
changes side, and a closed walk returns to its starting side: `Odd (count) ↔ side u ≠ side u`,
which is false (`key`).  (Pairs that are not edges of `T` are counted `0` times, in particular
`count` is even.)

The two steps are pure `Bool`/parity bookkeeping and are done locally below.
-/
import Mathlib

set_option autoImplicit false

universe u

namespace Work.ORDunwoody.Tracks

open scoped Sym2

theorem even_edges_count {V : Type u} [DecidableEq V] (T : SimpleGraph V) (hT : T.IsAcyclic)
    {u : V} (w : T.Walk u u) (e : Sym2 V) : Even (w.edges.count e) := by
  classical
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : T.Adj x y
    · -- `s(x, y)` is a genuine edge of the forest, hence a bridge: cut the tree in two.
      have hbridge : T.IsBridge s(x, y) :=
        (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT) hxy
      -- `side z` records on which of the two sides of the bridge `s(x, y)` the vertex `z` lies.
      set side : V → Bool := fun z => decide ((T.deleteEdges {s(x, y)}).Reachable x z) with hside
      -- The two sides of a bridge `s(x,y)`: a walk crosses from one side to the other exactly
      -- when it traverses the cut edge.
      have cut : ∀ p q : V, T.Adj p q → ((side p ≠ side q) ↔ s(p, q) = s(x, y)) := by
        intro p q hpq
        rw [hside]
        constructor
        · -- if the traversed edge is not `s(x, y)`, it survives in `T.deleteEdges {s(x, y)}`,
          -- so the two endpoints are on the same side
          intro hne
          by_contra h
          apply hne
          have hadj : (T.deleteEdges {s(x, y)}).Adj p q := by
            rw [SimpleGraph.deleteEdges_adj]
            exact ⟨hpq, by simpa using h⟩
          rw [decide_eq_decide]
          exact ⟨fun hp => hp.trans hadj.reachable, fun hq => hq.trans hadj.reachable.symm⟩
        · -- the cut edge itself joins the two sides: one endpoint is `x` (same side as `x`),
          -- the other is `y`, which is not reachable from `x` any more
          intro heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [ne_eq, decide_eq_decide]
            intro h
            exact hbridge (h.mp (SimpleGraph.Reachable.refl p))
          · rw [ne_eq, decide_eq_decide]
            intro h
            exact hbridge (h.mpr (SimpleGraph.Reachable.refl q))
      -- Parity of the number of traversals of the bridge, along an arbitrary walk.
      have key : ∀ {a b : V} (w : T.Walk a b), Odd (w.edges.count s(x,y)) ↔ (side a ≠ side b) := by
        intro a b w
        induction w with
        | nil => simp
        | @cons p q r hab w' ih =>
          rw [SimpleGraph.Walk.edges_cons, List.count_cons, Nat.odd_add, ih]
          have hk : Even (if (s(p,q) == s(x,y)) = true then 1 else 0) ↔ (side p = side q) := by
            by_cases h : s(p,q) = s(x,y)
            · have hne : side p ≠ side q := (cut p q hab).mpr h
              simp [h, hne]
            · have heq : side p = side q := by
                by_contra hc2
                exact h ((cut p q hab).mp hc2)
              simp [beq_iff_eq, h, heq]
          rw [hk]
          have boolkey : ∀ U V W : Bool, (((V ≠ W) ↔ (U = V)) ↔ (U ≠ W)) := by decide
          exact boolkey (side p) (side q) (side r)
      have hodd : ¬ Odd (w.edges.count s(x,y)) := by
        rw [key w]
        simp
      exact Nat.not_odd_iff_even.mp hodd
    · -- `s(x, y)` is not an edge of `T`, so `w` never traverses it and the count is `0`.
      have hmem : s(x, y) ∉ w.edges := fun hmem =>
        hxy (by simpa using w.edges_subset_edgeSet hmem)
      rw [List.count_eq_zero_of_not_mem hmem]
      simp

end Work.ORDunwoody.Tracks
