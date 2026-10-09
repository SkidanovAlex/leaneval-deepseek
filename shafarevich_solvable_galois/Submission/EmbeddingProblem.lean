/-
Copyright (c) 2025. All rights reserved.

# Embedding problems

The classical formulation of Shafarevich's theorem is in terms of *embedding problems*:
given a finite Galois extension `L/k` with group `H` and a surjection `π : G → H` of finite
groups (so that `1 → A → G → H → 1` is exact with `A = ker π`), one asks for a finite Galois
extension `L'/k` containing `L` such that `Gal(L'/k) ≅ G` compatibly with `π`.

This file defines the data and the notion of a solution, together with the trivial
consequences:
* a solution makes `G` realizable over `k` (`EmbeddingProblem.isSolvable_realizable`),
* every embedding problem with trivial kernel is solvable
  (`EmbeddingProblem.isSolvable_of_injective`).
-/
import Mathlib
import Submission.Realization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open scoped Classical

/-- An embedding problem over a field `k`: a finite Galois extension `L/k` together with a
surjective homomorphism from a finite group `G` onto `Gal(L/k)`.  (Traditionally the surjection
is the data of an exact sequence `1 → A → G → H → 1` with `H = Gal(L/k)` and `A = ker π`.) -/
structure EmbeddingProblem (k : Type*) [Field k] where
  /-- the field realizing the quotient group -/
  L : Type
  field : Field L
  algebra : Algebra k L
  finiteDimensional : FiniteDimensional k L
  isGalois : IsGalois k L
  /-- the group to be embedded -/
  G : Type
  group : Group G
  finite : Finite G
  /-- the projection onto the Galois group -/
  π : G →* (L ≃ₐ[k] L)
  surjective : Function.Surjective π

attribute [instance] EmbeddingProblem.field EmbeddingProblem.algebra
  EmbeddingProblem.finiteDimensional EmbeddingProblem.isGalois
  EmbeddingProblem.group EmbeddingProblem.finite

namespace EmbeddingProblem

variable {k : Type*} [Field k] (E : EmbeddingProblem k)

/-- A *solution* of an embedding problem `E`: a finite Galois extension `L'/k` containing `L`
(with `L'/L` Galois) and an isomorphism `G ≃* Gal(L'/k)` whose composite with the restriction
`Gal(L'/k) → Gal(L/k)` is `π`.  Concretely `Gal(L'/L)` is identified with the kernel of `π`. -/
def IsSolvable : Prop :=
  ∃ (L' : Type) (_ : Field L') (_ : Algebra k L') (_ : FiniteDimensional k L')
      (_ : IsGalois k L')
      (_ : Algebra E.L L') (_ : IsScalarTower k E.L L') (_ : FiniteDimensional E.L L')
      (_ : IsGalois E.L L'),
    ∃ (e : E.G ≃* (L' ≃ₐ[k] L')), ∀ (g : E.G) (x : E.L),
      e g (algebraMap E.L L' x) = algebraMap E.L L' (E.π g x)

/-- A solution of an embedding problem realizes its group. -/
theorem isSolvable_realizable (h : E.IsSolvable) : RealizableOver k E.G := by
  obtain ⟨L', hF, hA, hFD, hGal, hA2, hST, hFD2, hGal2, e, he⟩ := h
  letI : Field L' := hF
  letI : Algebra k L' := hA
  letI : FiniteDimensional k L' := hFD
  letI : IsGalois k L' := hGal
  exact ⟨L', hF, hA, hFD, hGal, ⟨e⟩⟩

/-- If the projection of an embedding problem is injective (trivial kernel) then the problem is
solved by the base field itself. -/
theorem isSolvable_of_injective (h : Function.Injective E.π) : E.IsSolvable := by
  have hbij : Function.Bijective E.π := ⟨h, E.surjective⟩
  let e : E.G ≃* (E.L ≃ₐ[k] E.L) := MulEquiv.ofBijective E.π hbij
  refine ⟨E.L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, e, ?_⟩
  intro g x
  rfl

end EmbeddingProblem

end Submission
