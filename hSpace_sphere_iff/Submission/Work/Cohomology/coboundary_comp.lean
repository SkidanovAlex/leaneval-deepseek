/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `δ ∘ δ = 0` for the coboundary of a simplicial set

The cochain complex of a simplicial set `S` with coefficients in a commutative ring `R` is the
cosimplicial object `n ↦ (S _⦋n⦌ → R)` of `R`-modules, where a morphism `φ : ⦋n⦌ ⟶ ⦋m⦌` of
`SimplexCategory` acts by precomposition with `S.map φ.op`.  Its alternating coface differential
`∑ᵢ (-1)ⁱ S.δᵢ` is exactly `Submission.Cohomology.coboundary`, so the cosimplicial identity
`δ² = 0` is a special case of `AlgebraicTopology.AlternatingCofaceMapComplex.d_squared`.
-/
import Mathlib
import Submission.Work.Cohomology.Basic

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- Precomposition with the identity is the identity. -/
lemma precomp_id (R : Type) [CommRing R] {α : Type} :
    Submission.Cohomology.precomp R (id : α → α) = LinearMap.id := by
  ext g x; rfl

/-- Precomposition is contravariantly functorial. -/
lemma precomp_comp (R : Type) [CommRing R] {α β γ : Type} (f : β → γ) (g : α → β) :
    Submission.Cohomology.precomp R (f ∘ g) =
      (Submission.Cohomology.precomp R g).comp (Submission.Cohomology.precomp R f) := by
  ext h x; rfl

/-- The cosimplicial object of `R`-valued cochains on a simplicial set `S`.

In degree `n` it is the `R`-module of functions `S _⦋n⦌ → R`; the structure map of a morphism
`φ : ⦋n⦌ ⟶ ⦋m⦌` of `SimplexCategory` is precomposition with the induced map `S.map φ.op`. -/
def cochainCosimplicial (S : SSet.{0}) (R : Type) [CommRing R] :
    CosimplicialObject (ModuleCat R) where
  obj n := ModuleCat.of R (S.obj (op n) → R)
  map {_ _} φ := ModuleCat.ofHom (Submission.Cohomology.precomp R (S.map φ.op))
  map_id n := by
    show ModuleCat.ofHom
        (Submission.Cohomology.precomp R
          ⇑(ConcreteCategory.hom (S.map (𝟙 n).op))) = 𝟙 _
    have h : S.map (𝟙 n).op = 𝟙 (S.obj (op n)) := by
      rw [show (𝟙 n).op = 𝟙 (op n) from rfl, CategoryTheory.Functor.map_id]
    rw [h, CategoryTheory.hom_id]
    exact ModuleCat.ofHom_id
  map_comp φ ψ := by
    show ModuleCat.ofHom (Submission.Cohomology.precomp R
          ⇑(ConcreteCategory.hom (S.map (φ ≫ ψ).op))) =
        ModuleCat.ofHom (Submission.Cohomology.precomp R
            ⇑(ConcreteCategory.hom (S.map φ.op))) ≫
          ModuleCat.ofHom (Submission.Cohomology.precomp R
            ⇑(ConcreteCategory.hom (S.map ψ.op)))
    rw [← ModuleCat.ofHom_comp]
    congr 1
    rw [← precomp_comp]
    congr 1
    rw [show (φ ≫ ψ).op = ψ.op ≫ φ.op from rfl, CategoryTheory.Functor.map_comp,
      CategoryTheory.hom_comp]

/-- The coface maps of `cochainCosimplicial` are given by the coboundary pieces. -/
lemma cochainCosimplicial_δ (S : SSet.{0}) (R : Type) [CommRing R] {m : ℕ} (i : Fin (m + 2)) :
    (cochainCosimplicial S R).δ i =
      ModuleCat.ofHom (Submission.Cohomology.precomp R (S.δ i)) := rfl

/-- The alternating coface differential of `cochainCosimplicial` is the coboundary. -/
lemma objD_hom_eq (S : SSet.{0}) (R : Type) [CommRing R] (m : ℕ) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cochainCosimplicial S R) m).hom
      = Submission.Cohomology.coboundary S R m := by
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    Submission.Cohomology.coboundary]
  apply Finset.sum_congr rfl
  intro i _
  show ModuleCat.Hom.hom ((-1 : ℤ) ^ (i : ℕ) •
        ModuleCat.ofHom (Submission.Cohomology.precomp R (S.δ i)))
      = (-1 : ℤ) ^ (i : ℕ) • Submission.Cohomology.precomp R (S.δ i)
  rw [ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]

theorem coboundary_comp (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    (Submission.Cohomology.coboundary S R (n + 1)).comp
      (Submission.Cohomology.coboundary S R n) = 0 := by
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cochainCosimplicial S R) n
  have h2 := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  rw [objD_hom_eq S R (n + 1), objD_hom_eq S R n] at h2
  exact h2

end Work.Cohomology
