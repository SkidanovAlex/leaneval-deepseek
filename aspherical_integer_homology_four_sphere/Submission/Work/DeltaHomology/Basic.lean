import Mathlib
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Delta-complexes (finite semi-simplicial sets)

This file defines the combinatorial input used to compute the homology of the
spaces built in the main project: a **finite `Δ`-complex** in the sense of
Hatcher §2.1, the weak form of a simplicial set in which only the face maps are
recorded (no degeneracies) and in which the `k`-simplices form a *finite* set
`Fin (K.card k)`.

The structure carries

* `dim` and `card k` — the number of `k`-simplices, zero above `dim`;
* `face σ i` — the `i`-th face of the `(k+1)`-simplex `σ`, a `k`-simplex;
* the semi-simplicial (face) identities `d_i d_j = d_{j-1} d_i` for `i < j`,
  written in the `Fin.succ`/`Fin.castSucc` form
  `face (face σ (Fin.succ j)) i = face (face σ (Fin.castSucc i)) j` for `i ≤ j`.

Everything downstream (the free chain complex `K.chain` in
`Submission/Work/DeltaHomology/Chain.lean`, and the comparison with singular
homology in `Submission/Work/DeltaHomology/Realization.lean`) builds on these
conventions.

## Conventions

* The `k`-simplices are the elements of `Fin (K.card k)`.  There is no
  combinatorial condition forcing faces of distinct simplices to be distinct:
  identifications are encoded in the data (`face` may be non-injective).
* `face σ i` for `σ : Fin (K.card (k+1))` and `i : Fin (k+2)` is the face
  *opposite* to the `i`-th vertex, exactly as in Hatcher's `Δ`-complexes.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.DeltaHomology

noncomputable section

/-- A finite `Δ`-complex (semi-simplicial set): a `ℕ`-indexed family of finite
sets of simplices with face maps satisfying the semi-simplicial identities, and
vanishing above the dimension `dim`. -/
structure DeltaCx where
  /-- An upper bound for the dimension (i.e. `card k = 0` for `k > dim`). -/
  dim : ℕ
  /-- The number of `k`-simplices. -/
  card : ℕ → ℕ
  /-- The `i`-th face of a `(k+1)`-simplex, a `k`-simplex. -/
  face : ∀ {k : ℕ}, Fin (card (k + 1)) → Fin (k + 2) → Fin (card k)
  /-- The semi-simplicial identities `d_i d_j = d_{j-1} d_i` (`i < j`), in the
  normal form `d_i d_{j+1} = d_j d_i` (`i ≤ j`). -/
  face_face : ∀ {k : ℕ} (σ : Fin (card (k + 2))) (i j : Fin (k + 2)), i ≤ j →
    face (face σ (Fin.succ j)) i = face (face σ (Fin.castSucc i)) j
  /-- There are no simplices above the dimension. -/
  card_eq_zero : ∀ k : ℕ, dim < k → card k = 0

namespace DeltaCx

variable (K L M : DeltaCx)

/-- Restatement of `DeltaCx.card_eq_zero`. -/
theorem card_eq_zero' {k : ℕ} (h : K.dim < k) : K.card k = 0 := K.card_eq_zero k h

/-- There are no `k`-simplices above the dimension; in particular `Fin (K.card k)`
is empty there. -/
theorem isEmpty_fin_card {k : ℕ} (h : K.dim < k) : IsEmpty (Fin (K.card k)) := by
  rw [K.card_eq_zero' h]; infer_instance

/-- The (weak) face identity in the equivalent form `d_i d_j = d_{j-1} d_i`,
`i < j`, stated with `Fin.pred`. -/
theorem face_face_pred {k : ℕ} (σ : Fin (K.card (k + 2))) (i : Fin (k + 2))
    (j : Fin (k + 3)) (hj : j ≠ 0) (hij : (i : ℕ) < (j : ℕ)) :
    K.face (K.face σ j) i = K.face (K.face σ (Fin.castSucc i)) (j.pred hj) := by
  have hle : i ≤ j.pred hj := by
    rw [Fin.le_iff_val_le_val, Fin.val_pred]
    omega
  have h := K.face_face σ i (j.pred hj) hle
  rwa [Fin.succ_pred] at h

/-- The iterated face maps: applying `face i` after `face j` for `i < j` lowers
the index. -/
theorem face_face_castSucc {k : ℕ} (σ : Fin (K.card (k + 2))) (i j : Fin (k + 2)) (h : i ≤ j) :
    K.face (K.face σ (Fin.succ j)) i = K.face (K.face σ (Fin.castSucc i)) j :=
  K.face_face σ i j h

/-- Simplicial maps of `Δ`-complexes: a dimension-preserving map of simplices
commuting with the face maps. -/
structure Hom (K L : DeltaCx) where
  /-- The map on `k`-simplices. -/
  map : ∀ {k : ℕ}, Fin (K.card k) → Fin (L.card k)
  /-- Compatibility with faces. -/
  map_face : ∀ {k : ℕ} (σ : Fin (K.card (k + 1))) (i : Fin (k + 2)),
    map (K.face σ i) = L.face (map σ) i

namespace Hom

variable {K L M N}

/-- The identity simplicial map. -/
protected def id (K : DeltaCx) : Hom K K where
  map := fun σ => σ
  map_face := fun _ _ => rfl

/-- Composition of simplicial maps. -/
protected def comp (f : Hom K L) (g : Hom L M) : Hom K M where
  map := fun σ => g.map (f.map σ)
  map_face := fun {k} σ i => by
    rw [f.map_face, g.map_face]

@[ext]
theorem ext {f g : Hom K L} (h : ∀ {k : ℕ} (σ : Fin (K.card k)), f.map σ = g.map σ) : f = g := by
  obtain ⟨fm, fp⟩ := f
  obtain ⟨gm, gp⟩ := g
  congr
  funext k σ
  exact h σ

@[simp]
theorem id_map (K : DeltaCx) {k : ℕ} (σ : Fin (K.card k)) : (Hom.id K).map σ = σ := rfl

@[simp]
theorem comp_map (f : Hom K L) (g : Hom L M) {k : ℕ} (σ : Fin (K.card k)) :
    (f.comp g).map σ = g.map (f.map σ) := rfl

@[simp]
theorem id_comp (f : Hom K L) : (Hom.id K).comp f = f := by
  ext σ; rfl

@[simp]
theorem comp_id (f : Hom K L) : f.comp (Hom.id L) = f := by
  ext σ; rfl

theorem comp_assoc (f : Hom K L) (g : Hom L M) (h : Hom M N) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

end Hom

/-- `Δ`-complexes and simplicial maps form a category. -/
instance : Category DeltaCx where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp := fun f => Hom.id_comp f
  assoc := fun f g h => Hom.comp_assoc f g h

@[simp] theorem id_eq (K : DeltaCx) : (𝟙 K : K ⟶ K) = Hom.id K := rfl
@[simp] theorem comp_eq (f : K ⟶ L) (g : L ⟶ M) : (f ≫ g) = f.comp g := rfl

end DeltaCx

end

end Work.DeltaHomology
