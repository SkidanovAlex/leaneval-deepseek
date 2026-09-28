import Mathlib
import Submission.Work.RatHurewicz.cellDefs

/-!
# The weight of a raw point of the model is constant on the classes of the gluing relation

`Work.RatHurewicz.rawWeight D a` is the size of the support of `a` when `a` is a point of a copy of
`Δ^{n+1}`, and `1` when `a` lies in a copy of the arc.  This file proves that it is an invariant of
the gluing relation `modelRel D` (hence of the equivalence relation it generates), i.e. that a class
of `Raw D` has a well defined "cell dimension".

The three generating relations are handled as follows.

* Two faces of copies of top cells: a face of a simplex is the simplex whose support is the image of
  the support under the injective map `Fin.succAbove p`, so the two supports have the same
  cardinality (`card_ptSupport_face`, via the general `card_rawSupp_map`).
* A vertex glued to the `0`-end of an arc: a vertex has a one-element support
  (`card_ptSupport_vertex`).
* The `1`-ends of two arcs: both have weight `1` by definition.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The support of a point of a standard simplex, for an arbitrary index type

`ptSupport` is defined only for the index type `Fin (n + 2)` (so that it can be used at the arity of
the faces of the top cells of the model), while the faces themselves live on `Fin (n + 1)`.  We
introduce the same construction for an arbitrary `Fin M` and record the trivial relation between the
two. -/

/-- The support of a point of `stdSimplex ℝ (Fin M)`: the set of vertices at which the barycentric
coordinate is nonzero. -/
def rawSupp {M : ℕ} (x : stdSimplex ℝ (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun i => (x : Fin M → ℝ) i ≠ 0)

theorem mem_rawSupp {M : ℕ} {x : stdSimplex ℝ (Fin M)} {i : Fin M} :
    i ∈ rawSupp x ↔ (x : Fin M → ℝ) i ≠ 0 :=
  Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩

/-- `ptSupport` and `rawSupp` are the same construction. -/
theorem ptSupport_eq_rawSupp (x : stdSimplex ℝ (Fin (n + 2))) : ptSupport x = rawSupp x := by
  ext k
  exact mem_ptSupport.trans mem_rawSupp.symm

/-! ## The support of a face

`stdSimplex.map f x` has, at the vertex `j`, the barycentric coordinate `∑_{f i = j} x i`; since the
coordinates of `x` are nonnegative this sum is nonzero exactly when one of its terms is, i.e. exactly
when `j` lies in the image of the support of `x`. -/

theorem map_apply_eq_sum {m k : ℕ} (f : Fin m → Fin k) (x : stdSimplex ℝ (Fin m)) (j : Fin k) :
    (stdSimplex.map f x : Fin k → ℝ) j
      = ∑ i ∈ (Finset.univ.filter (fun i : Fin m => f i = j)), x i := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]

theorem rawSupp_map_eq_image {m k : ℕ} (f : Fin m → Fin k) (x : stdSimplex ℝ (Fin m)) :
    rawSupp (stdSimplex.map f x) = (rawSupp x).image f := by
  ext j
  rw [mem_rawSupp, Finset.mem_image]
  rw [map_apply_eq_sum]
  constructor
  · intro hsum
    by_contra hcon
    push Not at hcon
    exact hsum (Finset.sum_eq_zero fun i hi => by
      by_contra hxi
      exact hcon i (by rw [mem_rawSupp]; exact hxi) (Finset.mem_filter.mp hi).2)
  · rintro ⟨i, hi, hfi⟩
    rw [mem_rawSupp] at hi
    have hmem : i ∈ Finset.univ.filter (fun i : Fin m => f i = j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hfi⟩
    have hle : x i ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin m => f i = j)), x i :=
      Finset.single_le_sum (fun i _ => x.2.1 i) hmem
    have hpos : 0 < x i := lt_of_le_of_ne (x.2.1 i) (Ne.symm hi)
    exact ne_of_gt (lt_of_lt_of_le hpos hle)

/-- An injective reindexing does not change the size of the support. -/
theorem card_rawSupp_map {m k : ℕ} {f : Fin m → Fin k} (hf : Function.Injective f)
    (x : stdSimplex ℝ (Fin m)) :
    (rawSupp (stdSimplex.map f x)).card = (rawSupp x).card := by
  rw [rawSupp_map_eq_image, Finset.card_image_of_injective _ hf]

/-- **The weight of a face depends only on the simplex, not on the face map**: the `p`-th face of
`x` is `x` reindexed by the injection `Fin.succAbove p`. -/
theorem card_ptSupport_face (p : Fin (n + 2)) (x : stdSimplex ℝ (Fin (n + 1))) :
    (ptSupport ((facept (n + 1) p) x)).card = (rawSupp x).card := by
  rw [show ((facept (n + 1) p) x) = stdSimplex.map p.succAbove x from rfl]
  rw [ptSupport_eq_rawSupp, card_rawSupp_map (Fin.succAbove_right_injective)]

/-! ## The weight of a vertex -/

theorem ptSupport_vertex (i : Fin (n + 2)) :
    ptSupport (stdSimplex.vertex (S := ℝ) i) = {i} := by
  ext k
  rw [mem_ptSupport, stdSimplex.vertex_coe, Finset.mem_singleton]
  by_cases h : k = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; simp [h]

theorem card_ptSupport_vertex (i : Fin (n + 2)) :
    (ptSupport (stdSimplex.vertex (S := ℝ) i)).card = 1 := by
  rw [ptSupport_vertex, Finset.card_singleton]

/-! ## The invariance of the weight -/

/-- **The generating relations of `modelRel D` preserve the weight.** -/
theorem rawWeight_rel (D : MData X n x₀) {a b : Raw D} (h : modelRel D a b) :
    rawWeight D a = rawWeight D b := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hsimp⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
  · rw [rawWeight_inl, rawWeight_inl, card_ptSupport_face, card_ptSupport_face]
  · rw [rawWeight_inl, rawWeight_inr, card_ptSupport_vertex]
  · rw [rawWeight_inr, rawWeight_inr]

/-- **The weight of a point of `Raw D` is constant on the equivalence classes of the gluing
relation.** -/
theorem rawWeight_eqvGen {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) {a b : Work.RatHurewicz.Raw D}
    (h : Relation.EqvGen (Work.RatHurewicz.modelRel D) a b) :
    Work.RatHurewicz.rawWeight D a = Work.RatHurewicz.rawWeight D b := by
  induction h with
  | rel x y hr => exact rawWeight_rel D hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

end

end Work.RatHurewicz
