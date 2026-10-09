/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The single-prime step of the reduction of Theorem 14

Schmidt–Wingberg, arXiv:math/9809211, §5:

> Since a finite nilpotent group is the direct product of its `p`-Sylow subgroups and since every
> finite `G`-operator `p`-group is a quotient of `F^(n)/F^(n)(ν)` for some `n, ν`, it suffices to
> show [the generic kernel statement] for every prime `p`.

This file proves the "quotient" half of that sentence: from the generic-kernel hypothesis for a
single prime `p` (`GenericKernelSolvableInClosure`, see `Defs.lean`) one obtains a proper solution
of *every* split embedding problem over `ℚ` with kernel a finite `G`-operator `p`-group.

The two inputs are

* `Work.GenericKernelReduction.exists_equivariant_quotient_freePQuotient`: every finite
  `G`-operator `p`-group `N` is a `G`-equivariant quotient `F^(n)/F^(n)(ν) ↠ N` of a generic
  kernel (`Work.ProP`, the `G`-operator refinement of the generic-kernel corollary), and
* `Work.GenericKernelReduction.inClosure_of_surjective`: a solution of the embedding problem with
  kernel `A` descends to a solution of the embedding problem with any quotient kernel
  `A ⋊ G ↠ N ⋊ G` of it that is a map of extensions over `G` (take the fixed field of the kernel).

Together they say: solve the problem for the generic kernel `F^(n)/F^(n)(ν)` (the hypothesis) and
push down to the arbitrarily given `p`-group `N`.
-/

import Submission.Work.GenericKernelReduction.Defs
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
