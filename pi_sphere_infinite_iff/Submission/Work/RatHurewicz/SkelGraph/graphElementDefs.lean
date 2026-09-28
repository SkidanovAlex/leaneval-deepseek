import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.points

/-!
# Auxiliary definitions for `Work.RatHurewicz.SkelGraph.graphElement`

A low dimensional point `y` of `Raw D` is either a vertex of a copy of a simplex, or a point with
two nonzero barycentric coordinates on a `1`-face, or a point of an arc.  The canonical form of
such a point is encoded by `decomp`, and `wOf` turns it into an element of the abstract graph
`V D ⊕ (E D × I)`.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology Simplicial unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The support of a point of a standard simplex: the set of coordinates that are nonzero. -/
def supp {m : ℕ} (x : stdSimplex ℝ (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun k => x.1 k ≠ 0)

theorem mem_supp {m : ℕ} {x : stdSimplex ℝ (Fin m)} {k : Fin m} :
    k ∈ supp x ↔ x.1 k ≠ 0 := by
  simp [supp]

theorem supp_nonempty {m : ℕ} (x : stdSimplex ℝ (Fin m)) : (supp x).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hzero : (∑ i : Fin m, x.1 i) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have : i ∉ supp x := by rw [h]; exact Finset.notMem_empty i
    simpa [supp] using this
  have h1 : (∑ i : Fin m, x.1 i) = 1 := x.2.2
  rw [h1] at hzero
  exact one_ne_zero hzero

theorem min'_ne_max' {m : ℕ} (x : stdSimplex ℝ (Fin m)) (h1 : (supp x).card ≠ 1) :
    (supp x).min' (supp_nonempty x) ≠ (supp x).max' (supp_nonempty x) := by
  intro h
  apply h1
  rw [Finset.card_eq_one]
  refine ⟨(supp x).min' (supp_nonempty x), ?_⟩
  ext k
  rw [Finset.mem_singleton]
  constructor
  · intro hk
    have hle1 : (supp x).min' (supp_nonempty x) ≤ k := Finset.min'_le _ _ hk
    have hle2 : k ≤ (supp x).max' (supp_nonempty x) := Finset.le_max' _ _ hk
    rw [← h] at hle2
    exact le_antisymm hle2 hle1
  · intro hk
    rw [hk]
    exact Finset.min'_mem _ _

theorem max'_le_one {m : ℕ} (x : stdSimplex ℝ (Fin m)) :
    x.1 ((supp x).max' (supp_nonempty x)) ≤ 1 := by
  have h := Finset.single_le_sum (s := supp x) (f := fun i => x.1 i)
    (fun i _ => x.2.1 i) (Finset.max'_mem (supp x) (supp_nonempty x))
  have hsum : (∑ i ∈ supp x, x.1 i) = 1 := by
    rw [← x.2.2]
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => ?_)
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  rwa [hsum] at h

/-- The canonical form of a point of a standard simplex: either a vertex (`Sum.inl`), or an
ordered pair of distinct vertices together with the parameter of the corresponding `1`-face
(`Sum.inr`).  The point is a vertex exactly when its support is a singleton; otherwise the two
elements of its support are used, in increasing order. -/
def decomp {m : ℕ} (x : stdSimplex ℝ (Fin m)) :
    Fin m ⊕ ({pq : Fin m × Fin m // pq.1 < pq.2} × I) :=
  if h1 : (supp x).card = 1 then
    Sum.inl ((supp x).min' (supp_nonempty x))
  else
    Sum.inr (⟨((supp x).min' (supp_nonempty x), (supp x).max' (supp_nonempty x)),
        Finset.min'_lt_max' _ (Finset.min'_mem _ _) (Finset.max'_mem _ _)
          (min'_ne_max' x h1)⟩,
      ⟨x.1 ((supp x).max' (supp_nonempty x)),
        x.2.1 _, max'_le_one x⟩)

/-- The image in the graph of a point of a copy of a simplex, using the canonical form. -/
def wSimp (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2))) : V D ⊕ (E D × I) :=
  match decomp x with
  | Sum.inl p => Sum.inl (vCl D (Sum.inl ⟨i, p⟩))
  | Sum.inr (e, s) => Sum.inr (eCl D (Sum.inl ⟨i, e⟩), s)

/-- The element of the abstract graph `V D ⊕ (E D × I)` attached to a low dimensional point of
`Raw D`. -/
def wOf (D : MData X n x₀) (y : {y : Raw D // isLowDim D y}) : V D ⊕ (E D × I) :=
  match y with
  | ⟨Sum.inl ⟨i, x⟩, _⟩ => wSimp D i x
  | ⟨Sum.inr ⟨i, s⟩, _⟩ => Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s)

@[simp] theorem wOf_inl_inl (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2)))
    (h : isLowDim D (Sum.inl ⟨i, x⟩)) (p : Fin (n + 2)) (hp : decomp x = Sum.inl p) :
    wOf D ⟨Sum.inl ⟨i, x⟩, h⟩ = Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) := by
  show wSimp D i x = _
  rw [wSimp, hp]

@[simp] theorem wOf_inl_inr (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2)))
    (h : isLowDim D (Sum.inl ⟨i, x⟩))
    (e : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2}) (s : I)
    (hp : decomp x = Sum.inr (e, s)) :
    wOf D ⟨Sum.inl ⟨i, x⟩, h⟩ = Sum.inr (eCl D (Sum.inl ⟨i, e⟩), s) := by
  show wSimp D i x = _
  rw [wSimp, hp]

@[simp] theorem wOf_inr (D : MData X n x₀) (i : D.Idx) (s : I)
    (h : isLowDim D (Sum.inr ⟨i, s⟩)) :
    wOf D ⟨Sum.inr ⟨i, s⟩, h⟩ = Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s) := rfl

end

end Work.RatHurewicz.SkelGraph
