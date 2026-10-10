import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Submission.Work.GenericKernelReduction.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- `CanonicalSplitEmbeddingSolvedInClosure L N φ` says that the split embedding problem
`1 → N → N ⋊[φ] Gal(L/ℚ) → Gal(L/ℚ) → 1` has a proper solution inside `AlgebraicClosure ℚ`
whose `↥L`-algebra structure on the solution field `↥M` is the canonical inclusion.  Concretely:
there is a finite Galois extension `M/ℚ` inside `AlgebraicClosure ℚ` with `L ≤ M` and `M/L` Galois,
an `↥L`-algebra structure on `↥M` with `(algebraMap ↥L ↥M x : AlgebraicClosure ℚ) = x` for all
`x : ↥L`, and an isomorphism `N ⋊[φ] Gal(L/ℚ) ≃* Gal(M/ℚ)` compatible with the restriction. -/
def CanonicalSplitEmbeddingSolvedInClosure (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (N : Type*) [Group N] [Finite N]
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) : Prop :=
  ∃ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : L ≤ M)
    (_ : FiniteDimensional ℚ M) (_ : IsGalois ℚ M)
    (_ : Algebra ↥L ↥M) (_ : IsScalarTower ℚ ↥L ↥M)
    (_ : FiniteDimensional ↥L ↥M) (_ : IsGalois ↥L ↥M)
    (_ : ∀ y : ↥L, (algebraMap ↥L ↥M y : AlgebraicClosure ℚ) = y),
    ∃ (e : N ⋊[φ] (L ≃ₐ[ℚ] L) ≃* (M ≃ₐ[ℚ] M)), ∀ (g : N ⋊[φ] (L ≃ₐ[ℚ] L)) (x : ↥L),
      e g (algebraMap ↥L ↥M x) = algebraMap ↥L ↥M (SemidirectProduct.rightHom g x)

/-- Forgetting the canonicality of the algebra structure, a canonical solution is a solution in
the sense of `SplitEmbeddingSolvedInClosure`. -/
theorem splitEmbeddingSolvedInClosure_of_canonical {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {N : Type} [Group N] [Finite N]
    {φ : (L ≃ₐ[ℚ] L) →* MulAut N} (h : CanonicalSplitEmbeddingSolvedInClosure L N φ) :
    SplitEmbeddingSolvedInClosure L N φ := by
  obtain ⟨M, hLM, hfd, hgal, hAlg, hST, hfdL, hgalL, _coef, e, he⟩ := h
  exact ⟨M, hLM, hfd, hgal, hAlg, hST, hfdL, hgalL, e, he⟩

end Work.GenericKernelReduction
