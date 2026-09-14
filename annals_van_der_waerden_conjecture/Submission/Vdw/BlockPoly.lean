import Mathlib
import Submission.Vdw.GaloisAction

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The block polynomial of a block of roots (first steps of the structural
dictionary for the imprimitive slice)

For an irreducible `f ∈ ℤ[X]` whose Galois group is imprimitive with a block
`B` of size `k` and `m = n/k` blocks, the *structural dictionary* of the
imprimitive counting argument consists of the statements

* (`blockPoly`) the **block polynomial** `P_B = ∏_{i ∈ B} (X - α_i)` is monic of
  degree `k` and its coefficients lie in the field of definition `L` of the
  block, with `[L : ℚ] = m`;
* (`map_eq_prod_rootOf`) `f = ∏_{i} (X - α_i) = ∏_{\text{blocks}} P_{B_j}`, so
  `f` is *determined* by the coefficient tuple of `P_B` (the map
  `P ↦ Norm_{L/ℚ}P`);
* (`galRootPerm_rootOf`) the Galois action permutes the block polynomials,
  `σ • P_B = P_{σ • B}`, so that the number of distinct conjugates of `P_B` is
  exactly the number of blocks `m` (orbit–stabiliser);
* multiplicativity of the Mahler measure turns `f ∈ Box n H` into the
  constraint `∏_{σ : L → ℂ} M_0(P_B^σ) ≤ (n+1)(H+1)` on `P_B`.

This module sets up the vocabulary (`rootOf`, `blockPoly`) and proves the
elementary part: monicity, injectivity of the root indexing, and the
`Gal`-equivariance of the root indexing (the input to the orbit–stabiliser
count of the conjugates of `P_B`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

/-- The root of `p` in its splitting field whose index is `i`, under the
identification `rootFinEquiv` of the root set with `Fin p.natDegree`. -/
def rootOf (p : ℚ[X]) (hsep : p.Separable) (i : Fin p.natDegree) : p.SplittingField :=
  ((rootFinEquiv p hsep).symm i : p.rootSet p.SplittingField)

lemma rootOf_injective (p : ℚ[X]) (hsep : p.Separable) : Function.Injective (rootOf p hsep) := by
  intro i j h
  have h1 : (rootFinEquiv p hsep).symm i = (rootFinEquiv p hsep).symm j := Subtype.ext h
  exact (rootFinEquiv p hsep).symm.injective h1


/-- **Galois equivariance of the root indexing**: the root permutation
`galRootPerm p σ` is the `galFinHom p hsep σ`-reindexing of the roots. -/
lemma galRootPerm_symm_rootOf (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (i : Fin p.natDegree) :
    galRootPerm p σ ((rootFinEquiv p hsep).symm i)
      = (rootFinEquiv p hsep).symm (galFinHom p hsep σ i) := by
  rw [← Equiv.symm_apply_apply (rootFinEquiv p hsep)
    (galRootPerm p σ ((rootFinEquiv p hsep).symm i))]
  congr 1

/-- **The block polynomial**: the monic polynomial over the splitting field whose
roots are the roots of `p` indexed by the finite set `B`. -/
def blockPoly (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree)) :
    p.SplittingField[X] :=
  ∏ i ∈ B, (X - C (rootOf p hsep i))

lemma blockPoly_monic (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)

lemma blockPoly_natDegree (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).natDegree = B.card := by
  rw [blockPoly, natDegree_prod B _ (fun i _ => X_sub_C_ne_zero _)]
  simp

/-- **The Galois action permutes the block polynomials**: the set of roots of the
block polynomial of `B` is carried by `galRootPerm p σ` to the set of roots of
the block polynomial of the translate `galFinHom p hsep σ '' B`. -/
lemma galRootPerm_blockPoly_roots (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (B : Finset (Fin p.natDegree)) :
    galRootPerm p σ '' {x : p.rootSet p.SplittingField |
        ∃ i ∈ B, (rootFinEquiv p hsep).symm i = x}
      = {x : p.rootSet p.SplittingField |
        ∃ i ∈ B, (rootFinEquiv p hsep).symm (galFinHom p hsep σ i) = x} := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨i, hi, hyi⟩ := hy
    refine ⟨i, hi, ?_⟩
    rw [← hxy, ← hyi, galRootPerm_symm_rootOf]
  · rintro ⟨i, hi, hxi⟩
    refine ⟨(rootFinEquiv p hsep).symm i, ⟨i, hi, rfl⟩, ?_⟩
    rw [← hxi, galRootPerm_symm_rootOf]

end

end Submission.Vdw
