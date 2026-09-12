import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.convexHull_triangulation_rel

open scoped BigOperators
open Set

namespace Commons.Geometry.Convex.Hadwiger

/-! # Triangulation of a full-dimensional polytope by `n`-simplices

The `convexHull_triangulation_rel` commons result produces, for any nonempty
finite point set `S` in a finite-dimensional real Euclidean space `V`, a
triangulation of `convexHull S` by simplices whose dimension equals the affine
dimension `d` of the hull, with pairwise disjoint *intrinsic* (relative)
interiors.  When the hull is full-dimensional (`interior` nonempty, hence
`d = n` in `EuclideanSpace ℝ (Fin n)`) those simplices are genuine
`n`-simplices whose carriers are convex bodies, and pairwise disjoint
intrinsic interiors immediately give pairwise empty ambient interiors.
-/

namespace ptHull

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Wrap a convex compact nonempty set into a `ConvexBody`. -/
noncomputable def cellBody {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Set V)
    (hcv : Convex ℝ X) (hcpt : IsCompact X) (hne : X.Nonempty) : ConvexBody V :=
  ⟨X, hcv, hcpt, hne⟩

@[simp]
lemma coe_cellBody {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Set V)
    (hcv : Convex ℝ X) (hcpt : IsCompact X) (hne : X.Nonempty) :
    ((cellBody X hcv hcpt hne : ConvexBody V) : Set V) = X := rfl

/-- The ambient interior is contained in the intrinsic interior. -/
lemma int_subset_rel {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Set V) :
    interior s ⊆ intrinsicInterior ℝ s := by
  exact interior_subset_intrinsicInterior

/-- A full-dimensional convex hull has affine span the whole space. -/
lemma span_top_of_interior {n : ℕ} (S : Finset (E n))
    (hint : (interior (convexHull ℝ (S : Set (E n)))).Nonempty) :
    affineSpan ℝ (S : Set (E n)) = ⊤ := by
  exact affineSpan_eq_top_of_nonempty_interior (s := (S : Set (E n))) hint

/-- The affine dimension of a full-dimensional convex hull equals the ambient
dimension `n`. -/
lemma finrank_affineSpan_eq_n {n : ℕ} (S : Finset (E n))
    (hint : (interior (convexHull ℝ (S : Set (E n)))).Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (S : Set (E n))).direction = n := by
  rw [span_top_of_interior S hint]
  rw [AffineSubspace.direction_top, finrank_top]
  simp

/-- A generating set whose hull has nonempty interior is nonempty. -/
lemma nonempty_of_hull {n : ℕ} (S : Finset (E n))
    (hint : (interior (convexHull ℝ (S : Set (E n)))).Nonempty) : S.Nonempty := by
  by_contra h
  have hS : (S : Set (E n)) = ∅ := by
    ext x
    constructor <;> intro hx
    · exfalso; exact h ⟨x, hx⟩
    · simpa using hx
  rw [hS, convexHull_empty] at hint
  simp at hint

/-- The `interior (s ∩ t)` is contained in `interior s ∩ interior t`. -/
lemma interior_inter_subset {X : Type*} [TopologicalSpace X] (s t : Set X) :
    interior (s ∩ t) ⊆ interior s ∩ interior t := by
  intro x hx
  refine ⟨?_, ?_⟩
  · exact interior_mono (Set.inter_subset_left (s := s) (t := t)) hx
  · exact interior_mono (Set.inter_subset_right (s := s) (t := t)) hx

end ptHull

open ptHull

/-- Every full-dimensional polytope (convex hull of a finite set with
nonempty interior) can be triangulated into finitely many `n`-simplices
with pairwise disjoint interiors. -/
theorem polytope_triangulation (n : ℕ) :
    ∀ (S : Finset (EuclideanSpace ℝ (Fin n))),
      (interior (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))))).Nonempty →
      ∃ (ι : Type) (_ : Fintype ι),
        ∃ A : ι → ConvexBody (EuclideanSpace ℝ (Fin n)),
        ∃ w : ι → Fin (n + 1) → EuclideanSpace ℝ (Fin n),
          (⋃ i : ι, (A i : Set (EuclideanSpace ℝ (Fin n))) =
            convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) ∧
          (∀ i : ι, (A i : Set (EuclideanSpace ℝ (Fin n))) =
            convexHull ℝ (Set.range (w i))) ∧
          (∀ i : ι, AffineIndependent ℝ (w i)) ∧
          (∀ i j : ι, i ≠ j →
            interior ((A i : Set (EuclideanSpace ℝ (Fin n))) ∩
              (A j : Set (EuclideanSpace ℝ (Fin n)))) = ∅) := by
  classical
  intro S hint
  have hSne : S.Nonempty := nonempty_of_hull S hint
  have hd : Module.finrank ℝ (affineSpan ℝ (S : Set (E n))).direction = n :=
    finrank_affineSpan_eq_n S hint
  have hrel := convexHull_triangulation_rel (V := E n) S hSne
  change ∃ (ι : Type) (_ : Fintype ι), ∃ A : ι → Set (E n),
      ∃ w : ι → Fin (Module.finrank ℝ (affineSpan ℝ (S : Set (E n))).direction + 1) → (E n),
        (⋃ i : ι, A i = convexHull ℝ (S : Set (E n))) ∧
        (∀ i : ι, A i = convexHull ℝ (Set.range (w i))) ∧
        (∀ i : ι, AffineIndependent ℝ (w i)) ∧
        (∀ i j : ι, i ≠ j →
          Disjoint (intrinsicInterior ℝ (A i)) (intrinsicInterior ℝ (A j))) at hrel
  rw [hd] at hrel
  rcases hrel with ⟨ι, hι, A, w, hcov, hcell, hind, hdisj⟩
  letI : Fintype ι := hι
  have hAconv : ∀ i : ι, Convex ℝ (A i) := by
    intro i
    rw [hcell i]
    exact convex_convexHull ℝ (Set.range (w i))
  have hAcpt : ∀ i : ι, IsCompact (A i) := by
    intro i
    rw [hcell i]
    exact (Set.finite_range (w i)).isCompact_convexHull ℝ
  have hAne : ∀ i : ι, (A i).Nonempty := by
    intro i
    rw [hcell i]
    exact ⟨w i 0, subset_convexHull ℝ (Set.range (w i)) (by simp)⟩
  refine ⟨ι, hι, fun i => cellBody (A i) (hAconv i) (hAcpt i) (hAne i), w, ?_, ?_, ?_, ?_⟩
  · simpa [cellBody] using hcov
  · intro i
    simpa [cellBody] using hcell i
  · simpa using hind
  · intro i j hij
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hn
    rcases hn with ⟨x, hx⟩
    have hx1 : x ∈ interior (A i) :=
      interior_mono (Set.inter_subset_left (s := (A i)) (t := (A j))) hx
    have hx2 : x ∈ interior (A j) :=
      interior_mono (Set.inter_subset_right (s := (A i)) (t := (A j))) hx
    have hxAi : x ∈ intrinsicInterior ℝ (A i) := int_subset_rel (A i) hx1
    have hxAj : x ∈ intrinsicInterior ℝ (A j) := int_subset_rel (A j) hx2
    exact (Set.disjoint_left.mp (hdisj i j hij)) hxAi hxAj

end Commons.Geometry.Convex.Hadwiger
