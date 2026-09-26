import Mathlib
import Submission.Work.SG.Defs

/-!
# Bounds on dual (superbase) coordinates of a Selling-minimal reduction

All six Selling support graphs `sellingGraph i` (`i : Fin 6`) on the four superbase
indices `0,1,2,3` are connected, and every vertex is at distance at most `3` from vertex `0`.
Consequently, if an integer coordinate function `x : Fin 4 → ℤ` satisfies `x 0 = 0` and
`|x a - x b| ≤ 1` along every edge of such a graph, then `|x m| ≤ 3` for every `m`.

The general engine is a breadth-first-layer argument: `sellingLayer E k` is the list of
vertices reachable from `0` by a walk with at most `k` edges, and any `x` as above is bounded
by `k` on that layer. The six concrete graphs are then discharged by `decide`.
-/

namespace Work.SG

/-- The neighbours of `v` in the graph `E`, listed in a fixed order. -/
def sellingNbrs (E : List (Fin 4 × Fin 4)) (v : Fin 4) : List (Fin 4) :=
  (E.filter (fun e => e.1 = v)).map (·.2) ++ (E.filter (fun e => e.2 = v)).map (·.1)

/-- Vertices reachable from `0` by a walk in `E` with at most `k` edges. -/
def sellingLayer (E : List (Fin 4 × Fin 4)) : ℕ → List (Fin 4)
  | 0 => [0]
  | k + 1 => sellingLayer E k ++ (sellingLayer E k).flatMap (sellingNbrs E)

/-- Characterisation of the neighbour list: `v` is listed as a neighbour of `u` in `E` exactly
when one of the two ordered versions of `{u,v}` is an edge of `E`. -/
lemma mem_sellingNbrs {E : List (Fin 4 × Fin 4)} {u v : Fin 4} :
    v ∈ sellingNbrs E u ↔ ((u, v) ∈ E ∨ (v, u) ∈ E) := by
  simp only [sellingNbrs, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨a, ⟨ha, h1⟩, h2⟩ | ⟨a, ⟨ha, h2⟩, h1⟩)
    · obtain ⟨a1, a2⟩ := a
      exact Or.inl (by rw [← h1, ← h2]; exact ha)
    · obtain ⟨a1, a2⟩ := a
      exact Or.inr (by rw [← h1, ← h2]; exact ha)
  · rintro (h | h)
    · exact Or.inl ⟨(u, v), ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨(v, u), ⟨h, rfl⟩, rfl⟩

/-- Walk bound: if `x 0 = 0` and `|x a - x b| ≤ 1` along every edge of `E`, then
`|x m| ≤ k` for every `m` reachable from `0` by a walk with at most `k` edges. -/
lemma abs_le_of_mem_sellingLayer {x : Fin 4 → ℤ} {E : List (Fin 4 × Fin 4)}
    (hE : ∀ e ∈ E, |x e.1 - x e.2| ≤ 1) (h0 : x 0 = 0) :
    ∀ k (m : Fin 4), m ∈ sellingLayer E k → |x m| ≤ (k : ℤ) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    simp only [sellingLayer, List.mem_singleton] at hm
    subst hm
    simp [h0]
  | succ k ih =>
    intro m hm
    rw [sellingLayer, List.mem_append] at hm
    rcases hm with hm | hm
    · have := ih m hm; push_cast; omega
    · rw [List.mem_flatMap] at hm
      obtain ⟨u, hu, hmu⟩ := hm
      have hu' := ih u hu
      have hedge := mem_sellingNbrs.mp hmu
      have hstep : |x m| ≤ |x u| + 1 := by
        have h1 : |x m - x u| ≤ 1 := by
          rcases hedge with h | h
          · rw [abs_sub_comm]; exact hE (u, m) h
          · exact hE (m, u) h
        have h2 : |x m| = |x u + (x m - x u)| := by congr 1; ring
        rw [h2]
        have h3 : |x u + (x m - x u)| ≤ |x u| + |x m - x u| := abs_add_le _ _
        linarith
      push_cast; omega

/-- Every vertex is reachable from `0` by a walk of at most `3` edges in each of the six
Selling support graphs. -/
lemma mem_sellingLayer_three (i : Fin 6) (m : Fin 4) :
    m ∈ sellingLayer (sellingGraph i) 3 := by
  fin_cases i <;> fin_cases m <;> decide

theorem abs_le_three_of_sellingGraph (i : Fin 6) {x : Fin 4 → ℤ} (h0 : x 0 = 0)
    (hE : ∀ e ∈ Work.SG.sellingGraph i, |x e.1 - x e.2| ≤ 1) :
    ∀ m : Fin 4, |x m| ≤ 3 := by
  intro m
  exact le_trans (abs_le_of_mem_sellingLayer hE h0 3 m (mem_sellingLayer_three i m))
    (by norm_num)

end Work.SG
