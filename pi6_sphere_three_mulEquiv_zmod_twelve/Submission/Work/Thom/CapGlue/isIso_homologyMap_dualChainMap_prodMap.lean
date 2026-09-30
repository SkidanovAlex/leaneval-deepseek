import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.CapGlue.isIso_CohMap_of_homotopic_inv

/-!
# `B × φ` acts invertibly on cohomology

If `φ : C(P, Q)` and `ψ : C(Q, P)` are homotopy inverse to one another, then so are the induced maps
`ContinuousMap.prodMap (ContinuousMap.id B) φ : C(B × P, B × Q)` and
`ContinuousMap.prodMap (ContinuousMap.id B) ψ : C(B × Q, B × P)` of the product with a fixed space
`B`: indeed `(id_B × φ) ∘ (id_B × ψ) = id_B × (φ ∘ ψ)`, which is homotopic to `id_B × id_Q = id`,
and symmetrically.  Homotopy invariance of singular cohomology
(`Work.Thom.CohMap_homotopic`) therefore lets us read off

  `(B × φ)^* : Hⁿ(B × Q; R) ⟶ Hⁿ(B × P; R)`

as an isomorphism (`Work.Thom.CapGlue.isIso_CohMap_of_homotopic_inv`).

The statement below is the same fact expressed at the level of the cochain complexes, i.e. about the
homology of the dual chain map `Work.Cohomology.dualChainMap`, which is *definitionally* the
cohomology pullback `Work.Thom.CohMap`.  This is the form in which the naturality statements of the
Thom chapter consume it.
-/

namespace Work.Thom.CapGlue

open CategoryTheory

/-- The `prodMap` of two composites is the composite of the `prodMap`s. -/
private theorem prodMap_comp {A₁ A₂ A₃ B₁ B₂ B₃ : Type}
    [TopologicalSpace A₁] [TopologicalSpace A₂] [TopologicalSpace A₃]
    [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₃]
    (f : C(A₂, A₃)) (f' : C(A₁, A₂)) (g : C(B₂, B₃)) (g' : C(B₁, B₂)) :
    (ContinuousMap.prodMap f g).comp (ContinuousMap.prodMap f' g') =
      ContinuousMap.prodMap (f.comp f') (g.comp g') := by
  apply ContinuousMap.ext
  intro x
  cases x with
  | mk a b => rfl

/-- The `prodMap` of two identities is the identity. -/
private theorem prodMap_id {A B : Type} [TopologicalSpace A] [TopologicalSpace B] :
    ContinuousMap.prodMap (ContinuousMap.id A) (ContinuousMap.id B) =
      ContinuousMap.id (A × B) := by
  apply ContinuousMap.ext
  intro x
  cases x with
  | mk a b => rfl

theorem isIso_homologyMap_dualChainMap_prodMap {B P Q : Type} [TopologicalSpace B]
    [TopologicalSpace P] [TopologicalSpace Q] (φ : C(P, Q)) (ψ : C(Q, P))
    (h1 : (φ.comp ψ).Homotopic (ContinuousMap.id Q)) (h2 : (ψ.comp φ).Homotopic (ContinuousMap.id P))
    (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of (B × P)) (TopCat.of (B × Q))
      (TopCat.ofHom (ContinuousMap.prodMap (ContinuousMap.id B) φ))) n) := by
  have h1' : ((ContinuousMap.prodMap (ContinuousMap.id B) φ).comp
      (ContinuousMap.prodMap (ContinuousMap.id B) ψ)).Homotopic (ContinuousMap.id (B × Q)) := by
    rw [prodMap_comp, ← prodMap_id]
    exact ContinuousMap.Homotopic.prodMap (ContinuousMap.Homotopic.refl _) h1
  have h2' : ((ContinuousMap.prodMap (ContinuousMap.id B) ψ).comp
      (ContinuousMap.prodMap (ContinuousMap.id B) φ)).Homotopic (ContinuousMap.id (B × P)) := by
    rw [prodMap_comp, ← prodMap_id]
    exact ContinuousMap.Homotopic.prodMap (ContinuousMap.Homotopic.refl _) h2
  show CategoryTheory.IsIso (Work.Thom.CohMap (ContinuousMap.prodMap (ContinuousMap.id B) φ) R n)
  exact isIso_CohMap_of_homotopic_inv _ _ h1' h2' R n

end Work.Thom.CapGlue
