import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Submission.Work.GenericKernelReduction.exists_equivariant_quotient_freePQuotient
import Submission.Work.GenericKernelReduction.inClosure_of_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- **The single-prime step of the reduction of Theorem 14.**  If the generic-kernel hypothesis
holds (in the closure form of `Defs.lean`), then every split embedding problem over `ℚ` whose
kernel is a finite `G`-operator `p`-group has a proper solution inside `AlgebraicClosure ℚ`. -/
theorem splitEmbeddingSolvedInClosure_of_genericKernel_singlePrime
    (hgen : GenericKernelSolvableInClosure)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime] (N : Type) [Group N] [Finite N] (hN : IsPGroup p N)
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) :
    SplitEmbeddingSolvedInClosure L N φ := by
  classical
  -- the `G`-operator structure on `N` given by `φ`, definitionally
  letI : MulDistribMulAction (L ≃ₐ[ℚ] L) N := mdmaOfHom φ
  -- `N` is a `G`-equivariant quotient of a generic kernel
  obtain ⟨n, ν, ρ, Φ, f, hf, hdesc, heq⟩ :=
    exists_equivariant_quotient_freePQuotient (G := L ≃ₐ[ℚ] L) hN
  -- the induced surjection of split extensions over `G = Gal(L/ℚ)`
  have hmap : ∀ g : (L ≃ₐ[ℚ] L),
      f.comp (MulEquiv.toMonoidHom (Φ g))
        = (MulEquiv.toMonoidHom (φ ((MonoidHom.id (L ≃ₐ[ℚ] L)) g))).comp f := by
    intro g
    refine MonoidHom.ext fun y => ?_
    show f (Φ g y) = φ g (f y)
    rw [heq g y, toMulAut_mdmaOfHom]
  refine inClosure_of_surjective
    (f := SemidirectProduct.map f (MonoidHom.id (L ≃ₐ[ℚ] L)) hmap) ?_ ?_
    (hgen L p n ν ρ Φ hdesc)
  · intro x
    obtain ⟨a, ha⟩ := hf x.left
    refine ⟨SemidirectProduct.inl a * SemidirectProduct.inr x.right, ?_⟩
    simp [SemidirectProduct.map_inl, SemidirectProduct.map_inr, ha,
      SemidirectProduct.inl_left_mul_inr_right]
  · intro x
    simp [SemidirectProduct.map_right]

/-- The single-prime step in the unfolded form used by `Submission.splitEmbeddingTheoremOverRat`:
every split embedding problem over `ℚ` with finite `p`-group kernel has a proper solution. -/
theorem splitEmbeddingSolvable_of_genericKernel_singlePrime
    (hgen : GenericKernelSolvableInClosure)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime] (N : Type) [Group N] [Finite N] (hN : IsPGroup p N)
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) :
    Work.Fitting.SplitEmbeddingSolvable L N φ :=
  splitEmbeddingSolvable_of_inClosure
    (splitEmbeddingSolvedInClosure_of_genericKernel_singlePrime hgen L p N hN φ)

/-- The single-prime step at the level of realizability: if the generic-kernel hypothesis holds,
then for every finite `p`-group `N` with an action of `Gal(L/ℚ)`, the semidirect product
`N ⋊ Gal(L/ℚ)` is realizable over `ℚ`. -/
theorem realizableOver_of_genericKernel_singlePrime
    (hgen : GenericKernelSolvableInClosure)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime] (N : Type) [Group N] [Finite N] (hN : IsPGroup p N)
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) :
    Submission.RealizableOver ℚ (N ⋊[φ] (L ≃ₐ[ℚ] L)) :=
  Work.Fitting.realizableOver_of_splitEmbeddingSolvable
    (splitEmbeddingSolvable_of_genericKernel_singlePrime hgen L p N hN φ)

end Work.GenericKernelReduction
