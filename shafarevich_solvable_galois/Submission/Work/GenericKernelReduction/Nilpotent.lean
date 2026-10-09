/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# From a single prime to a finite nilpotent kernel

Schmidt–Wingberg, arXiv:math/9809211, §5: a finite nilpotent group is the direct product of its
Sylow subgroups, and these are *characteristic* (in a nilpotent group every Sylow subgroup is
normal, hence the unique Sylow subgroup for its prime), so the decomposition is compatible with
any operator action.  Combining the single-prime solutions for the Sylow subgroups — they are
automatically *linearly disjoint over `L`*, because the relative Galois group of the intersection
of the two realizations injects into both a `p`-group and a `q`-group — yields a solution for the
whole nilpotent kernel.

The inputs are

* `Work.GenericKernelReduction.sylow_decomposition_equivariant`: the Sylow decomposition of a
  finite nilpotent group, compatibly with an arbitrary action `φ : G →* MulAut N`;
* `Work.GenericKernelReduction.splitEmbeddingSolvedInClosure_pi`: the combination of solutions
  with pairwise coprime kernels over the common base field `L` (the compositum is the fibre
  product of the individual solutions over `Gal(L/ℚ)`);
* `Work.GenericKernelReduction.splitEmbeddingSolvedInClosure_of_mulEquiv`: transport along a
  `G`-equivariant isomorphism of kernels.
-/

import Submission.Work.GenericKernelReduction.Defs
import Submission.Work.GenericKernelReduction.Transport
import Submission.Work.GenericKernelReduction.SinglePrime
import Submission.Work.GenericKernelReduction.sylow_decomposition_equivariant
import Submission.Work.GenericKernelReduction.splitEmbeddingSolvedInClosure_pi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- **Theorem 14 for a finite nilpotent kernel, from the generic-kernel hypothesis.**  If the
generic-kernel hypothesis holds, then every split embedding problem over `ℚ` with finite nilpotent
kernel has a proper solution inside `AlgebraicClosure ℚ`. -/
theorem splitEmbeddingSolvedInClosure_of_genericKernel_nilpotent
    (hgen : GenericKernelSolvableInClosure)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (N : Type) [Group N] [Finite N] (hN : Group.IsNilpotent N)
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) : SplitEmbeddingSolvedInClosure L N φ := by
  classical
  -- the equivariant Sylow decomposition of `N`
  obtain ⟨P, hPp, _hPn, ψ, e, he, _hres⟩ := sylow_decomposition_equivariant hN φ
  -- the orders of distinct Sylow subgroups are coprime
  have hcop : Pairwise fun i j : (Nat.card N).primeFactors =>
      Nat.Coprime (Nat.card ↥(P i)) (Nat.card ↥(P j)) := by
    intro i j hij
    haveI : Fact (Nat.Prime (i : ℕ)) := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    haveI : Fact (Nat.Prime (j : ℕ)) := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    exact IsPGroup.coprime_card_of_ne (i : ℕ) (j : ℕ)
      (fun h => hij (Subtype.ext h)) (P i) (P j) (hPp i) (hPp j)
  -- the single-prime solutions combine
  have hfam : SplitEmbeddingSolvedInClosure L (∀ i, ↥(P i)) (piAction ψ) :=
    splitEmbeddingSolvedInClosure_pi (A := fun i : (Nat.card N).primeFactors => ↥(P i))
      hcop ψ (fun i =>
        haveI : Fact (Nat.Prime (i : ℕ)) := ⟨Nat.prime_of_mem_primeFactors i.2⟩
        splitEmbeddingSolvedInClosure_of_genericKernel_singlePrime hgen L (i : ℕ) (↥(P i))
          (hPp i) (ψ i))
  -- transport along the equivariant identification `N ≃ ∏_p P_p`
  refine splitEmbeddingSolvedInClosure_of_mulEquiv (e := e.symm) ?_ hfam
  intro g a
  have hpi : (piAction ψ) g a = (MulEquiv.piCongrRight fun p => ψ p g) a := by
    funext i; simp
  have h := he g (e.symm a)
  simp only [MulEquiv.apply_symm_apply] at h
  rw [show (piAction ψ) g a = e (φ g (e.symm a)) from hpi.trans h.symm]
  simp

/-- **Theorem 14 for a finite nilpotent kernel** (unfolded form): from the generic-kernel
hypothesis, every split embedding problem over `ℚ` with finite nilpotent kernel has a proper
solution. -/
theorem splitEmbeddingSolvable_of_genericKernel_nilpotent
    (hgen : GenericKernelSolvableInClosure)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (N : Type) [Group N] [Finite N] (hN : Group.IsNilpotent N)
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) :
    Work.Fitting.SplitEmbeddingSolvable L N φ :=
  splitEmbeddingSolvable_of_inClosure
    (splitEmbeddingSolvedInClosure_of_genericKernel_nilpotent hgen L N hN φ)

/-- **Theorem 14 for a finite nilpotent kernel**, at the level of realizability: for every finite
nilpotent group `N` with an action `φ` of `Gal(L/ℚ)`, the semidirect product `N ⋊[φ] Gal(L/ℚ)`
is realizable over `ℚ`.  This is the hypothesis of
`Work.Fitting.realizable_of_solvable_of_split_embedding_univ`. -/
theorem realizableOver_of_genericKernel_nilpotent
    (hgen : GenericKernelSolvableInClosure)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (N : Type) [Group N] [Finite N] (hN : Group.IsNilpotent N)
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) :
    Submission.RealizableOver ℚ (N ⋊[φ] (L ≃ₐ[ℚ] L)) :=
  Work.Fitting.realizableOver_of_splitEmbeddingSolvable
    (splitEmbeddingSolvable_of_genericKernel_nilpotent hgen L N hN φ)

end Work.GenericKernelReduction
