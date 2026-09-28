import Mathlib
import Submission.Work.RatHurewicz.cellFacts
import Submission.Work.RatHurewicz.avoidAux

/-!
# The shape invariant of the model, and uniqueness of representatives

`Work.RatHurewicz.shapeAt` (defined in `avoidAux.lean`) is the shape of a point of a copy of
`Δ^{n+1}`: the set of pairs `(rank, value)` of its nonzero barycentric coordinates; on the arcs it
takes the value `{(0,1)}` (the shape of a vertex).

The main results here:

* `shapeAt_modelRel` / `shapeAt_eqvGen`: the shape is invariant under the gluing relation
  `modelRel D` and under the equivalence relation it generates.  (Only the face gluing needs
  `shapeOf_facept`; the vertex/arc relations are immediate.)

* `eq_of_eqvGen_sameCopy`: **the representative of an open cell in a fixed copy is unique**: two
  related points of the same copy of `Δ^{n+1}` with the same support are equal.  This is the
  substitute for "the cells of the model are disjoint" that the cell-by-cell push needs.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ} {D : MData X n x₀}

/-! ## The shape of a vertex -/

theorem rankIn_singleton_eq_zero {m : ℕ} (a : Fin (m + 2)) :
    rankIn ({a} : Finset (Fin (m + 2))) a = 0 := by
  rw [rankIn, Finset.filter_singleton, if_neg (lt_irrefl a), Finset.card_empty]

theorem shapeOf_vertex {m : ℕ} (a : Fin (m + 2)) :
    shapeOf (stdSimplex.vertex (S := ℝ) a) = {(0, 1)} := by
  rw [shapeOf, suppOf_vertex, Finset.image_singleton, rankIn_singleton_eq_zero]
  simp [stdSimplex.vertex_coe]

/-! ## Invariance of the shape -/

@[simp] theorem shapeAt_inl (D : MData X n x₀) (i : D.Idx)
    (x : stdSimplex ℝ (Fin (n + 2))) : shapeAt D (Sum.inl ⟨i, x⟩) = shapeOf x := rfl

@[simp] theorem shapeAt_inr (D : MData X n x₀) (i : D.Idx) (t : unitInterval) :
    shapeAt D (Sum.inr ⟨i, t⟩) = {(0, 1)} := rfl

/-- The generating relations of the gluing preserve the shape. -/
theorem shapeAt_rel (D : MData X n x₀) {a b : Raw D} (h : modelRel D a b) :
    shapeAt D a = shapeAt D b := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, _⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
  · rw [shapeAt_inl, shapeAt_inl]
    exact (shapeOf_facept n p x).trans (shapeOf_facept n q x).symm
  · rw [shapeAt_inl, shapeAt_inr, shapeOf_vertex]
  · rw [shapeAt_inr, shapeAt_inr]

/-- **The shape of a raw point of the model is invariant under the gluing relation.** -/
theorem shapeAt_eqvGen (D : MData X n x₀) {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) : shapeAt D a = shapeAt D b := by
  induction h with
  | rel x y hr => exact shapeAt_rel D hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-! ## Uniqueness of the representative in a fixed copy -/

/-- **Two related points of the same copy of the standard simplex with the same support are
equal.**  Equivalently: on each open cell of the model, the copy of the cell in a fixed top cell is
injected into the model. -/
theorem eq_of_eqvGen_sameSupp {i : D.Idx} {x x' : stdSimplex ℝ (Fin (n + 2))}
    (h : Relation.EqvGen (modelRel D) (Sum.inl ⟨i, x⟩) (Sum.inl ⟨i, x'⟩))
    (hsupp : suppOf x = suppOf x') : x = x' := by
  have hshape : shapeOf x = shapeOf x' := by
    have h := shapeAt_eqvGen D h
    rwa [shapeAt_inl, shapeAt_inl] at h
  exact shapeOf_injOn hsupp hshape

/-- The `ptSupport` form of the uniqueness of the representative. -/
theorem eq_of_eqvGen_sameCopy {i : D.Idx} {x x' : stdSimplex ℝ (Fin (n + 2))}
    (h : Relation.EqvGen (modelRel D) (Sum.inl ⟨i, x⟩) (Sum.inl ⟨i, x'⟩))
    (hsupp : ptSupport x = ptSupport x') : x = x' :=
  eq_of_eqvGen_sameSupp h hsupp

/-- The `Quotient` form of the uniqueness of the representative. -/
theorem eq_of_quotient_eq_sameCopy {i : D.Idx} {x x' : stdSimplex ℝ (Fin (n + 2))}
    (h : (Quotient.mk'' (Sum.inl ⟨i, x⟩) : Model D) = Quotient.mk'' (Sum.inl ⟨i, x'⟩))
    (hsupp : ptSupport x = ptSupport x') : x = x' :=
  eq_of_eqvGen_sameCopy (Quotient.exact h) hsupp

end

end Work.RatHurewicz
