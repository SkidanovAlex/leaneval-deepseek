import Mathlib
import Submission.Work.SG.EdgeSetDefs

/-! ### `sellingVecs` depends only on the underlying undirected edge set

`sellingVecs E` is defined by the constraints `|x a − x b| ≤ 1` for the ordered pairs `(a,b) ∈ E`,
with `x = (0, y₀, y₁, y₂)`.  The constraint attached to `(a,b)` is symmetric in `a` and `b`
(absolute value), so the ordered list is irrelevant and only `edgeSet E`, the underlying set of
*unordered* pairs, matters.  Consequently two lists with the same `edgeSet` define the same set of
coset-minimal vectors.
-/

namespace Work.SG

/-- `sellingVecs` is antitone with respect to the underlying undirected edge set: adding edges (as
an unordered set) can only shrink the set of vectors.  Direction: `edgeSet E ⊆ edgeSet E'` means
`E'` imposes at least as many constraints as `E`, hence `sellingVecs E' ⊆ sellingVecs E`. -/
theorem sellingVecs_subset_of_edgeSet_subset {E E' : List (Fin 4 × Fin 4)}
    (h : edgeSet E ⊆ edgeSet E') : sellingVecs E' ⊆ sellingVecs E := by
  intro y hy
  refine ⟨hy.1, fun e he => ?_⟩
  -- the edge `e` of `E` occurs, as an unordered pair, in `E'`
  have hz : s(e.1, e.2) ∈ edgeSet E := mem_edgeSet.mpr ⟨e, he, rfl⟩
  obtain ⟨p, hp, hps⟩ := mem_edgeSet.mp (h hz)
  -- `hps : s(p.1, p.2) = s(e.1, e.2)`, so `p` is `e` or its swap
  have hcond : |(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) p.1
      - (Fin.cons (0 : ℤ) y : Fin 4 → ℤ) p.2| ≤ 1 := hy.2 p hp
  have hswap : p = e ∨ p = e.swap := Sym2.mk_eq_mk_iff.mp hps
  -- the value of the constraint is unchanged by swapping the two endpoints
  have hval : |(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) e.1
      - (Fin.cons (0 : ℤ) y : Fin 4 → ℤ) e.2| =
      |(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) p.1
      - (Fin.cons (0 : ℤ) y : Fin 4 → ℤ) p.2| := by
    rcases hswap with rfl | rfl
    · rfl
    · simp only [Prod.swap]
      rw [abs_sub_comm]
  rw [hval]
  exact hcond

theorem sellingVecs_edgeSet_eq {E E' : List (Fin 4 × Fin 4)}
    (h : edgeSet E = edgeSet E') : sellingVecs E = sellingVecs E' := by
  apply Set.Subset.antisymm
  · exact sellingVecs_subset_of_edgeSet_subset (le_of_eq h.symm)
  · exact sellingVecs_subset_of_edgeSet_subset (le_of_eq h)

end Work.SG
