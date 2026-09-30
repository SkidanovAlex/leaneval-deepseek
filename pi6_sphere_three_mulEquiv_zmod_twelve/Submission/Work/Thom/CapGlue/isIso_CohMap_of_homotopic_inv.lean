import Mathlib
import Submission.Work.Thom.Cohomology

namespace Work.Thom.CapGlue

open CategoryTheory

/-- **A homotopy equivalence induces an isomorphism on cohomology.**  If `f : C(X,Y)` and
`g : C(Y,X)` are homotopy inverse to one another, then the pullback `f^* : H^n(Y;R) → H^n(X;R)`
is an isomorphism, with inverse `g^*`: indeed `f ≫ g = (f ∘ g)^* = (id_Y)^* = 𝟙` and
`g ≫ f = (g ∘ f)^* = (id_X)^* = 𝟙` by homotopy invariance. -/
theorem isIso_CohMap_of_homotopic_inv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (h1 : (f.comp g).Homotopic (ContinuousMap.id Y))
    (h2 : (g.comp f).Homotopic (ContinuousMap.id X)) (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (CohMap f R n) := by
  have h1' : CohMap f R n ≫ CohMap g R n = 𝟙 (Coh R n Y) := by
    rw [← CohMap_comp g f R n, CohMap_homotopic h1 R n, CohMap_id]
  have h2' : CohMap g R n ≫ CohMap f R n = 𝟙 (Coh R n X) := by
    rw [← CohMap_comp f g R n, CohMap_homotopic h2 R n, CohMap_id]
  exact ⟨CohMap g R n, h1', h2'⟩

end Work.Thom.CapGlue
