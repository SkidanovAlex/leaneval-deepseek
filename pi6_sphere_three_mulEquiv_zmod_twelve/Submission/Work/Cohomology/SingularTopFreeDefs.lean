import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.Pullback

set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary definitions for the "top homology of an open subset of `ℝ^N` is free" development

* `Work.Cohomology.OnePointSpace N` — the one-point compactification of `ℝ^N`;
* `Work.Cohomology.inclSet h` — the inclusion of a subspace into a larger one, as a morphism of
  `TopCat`;
* `Work.Cohomology.toUnion V n` — the inclusion `V n ⊆ ⋃ k, V k`.

The main results live in `Submission/Work/Cohomology/euclidean_open_homology_top_free.lean`.
-/

namespace Work.Cohomology

/-- The one-point compactification of `ℝ^N`. -/
abbrev OnePointSpace (N : ℕ) : Type := OnePoint (EuclideanSpace ℝ (Fin N))

/-- The inclusion of a subspace into a larger one, as a morphism of `TopCat`. -/
def inclSet {X : TopCat} {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩,
    continuous_subtype_val.subtype_mk (fun x => h x.2)⟩

/-- The inclusion `V n ⊆ ⋃ k, V k`. -/
def toUnion {X : TopCat} (V : ℕ → Set X) (n : ℕ) :
    TopCat.of (V n) ⟶ TopCat.of (⋃ k, V k) :=
  inclSet (Set.subset_iUnion V n)

end Work.Cohomology
