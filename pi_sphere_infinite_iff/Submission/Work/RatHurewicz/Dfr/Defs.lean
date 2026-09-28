import Mathlib
import Submission.Work.Serre.ThomCylDefs

/-!
# Small vocabulary for the fibrewise restriction of the relative Thom class

`Work.RatHurewicz.Dfr.mapsToRestrict` is the continuous map `↥A → ↥B` induced by a continuous map
`f : C(X, Y)` sending `A ⊆ X` into `B ⊆ Y`.  It is the map whose pullback appears in the naturality
of the connecting homomorphism `Work.Cohomology.pairδ` of a pair.
-/

namespace Work.RatHurewicz.Dfr

/-- The restriction of a continuous map to a pair of subsets. -/
def mapsToRestrict {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) : C(↥A, ↥B) :=
  ⟨fun a => ⟨f a.1, hf a.1 a.2⟩,
    Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) (fun a => hf a.1 a.2)⟩

@[simp] theorem mapsToRestrict_coe {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (a : ↥A) :
    (mapsToRestrict f A B hf a : Y) = f a.1 := rfl

end Work.RatHurewicz.Dfr
