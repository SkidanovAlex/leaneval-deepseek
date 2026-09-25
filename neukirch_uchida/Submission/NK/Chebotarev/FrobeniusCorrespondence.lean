/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase

/-!
# (D) The Frobenius-preservation API for the reconstruction step

The Neukirch–Uchida proof reconstructs a field isomorphism from a homeomorphic isomorphism
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` by matching *Frobenius elements* at corresponding places.  This
file isolates precisely which statement is needed, proves the reduction, and records why the
naive group-theoretic formulation is false.

## 1. The exact correspondence

`NK.Chebotarev.MatchesFrobeniusAt φ P₁ P₂` is the statement that an isomorphism of Galois groups
`φ` matches the *sets of Frobenius elements* at the two primes `P₁`, `P₂`.  It is exactly the local
correspondence at the primes (Neukirch, *Cohomology of Number Fields*, XII (12.1.9)) in the form in
which the endgame consumes it, and it is **not** a consequence of `φ(Map D_{P₁}) = D_{P₂}`:
the decomposition group of a place is only determined up to its arithmetic structure, and an
arbitrary isomorphism of Galois groups may permute the Frobenius elements inside it.

The reduction is `IsFrobAt.map_of_matchesFrobeniusAt`.

## 2. What *is* a consequence of the group theory

`NK.Chebotarev.IsFrobAtConj`, `NK.Chebotarev.ConjugacyOfFrobenius`,
`NK.Chebotarev.FrobeniusGenerateTop` (the Frobenius elements generate a finite Galois group) and
`NK.Chebotarev.EquivDeterminedByFrobenius` (an isomorphism of Galois groups is determined by its
values on the Frobenius elements) are the group-theoretic half, and they are proved.

## 3. The arithmetic case, unconditionally

If the isomorphism of Galois groups is *induced by a field isomorphism* — i.e. it comes from an
`e : L₁ ≃ₐ[K] L₂` over a common base field — then Frobenius elements are preserved;
this is `NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase` (and its cyclotomic special case
`NK.Chebotarev.IsFrobAtPrimeAlgEquiv`).  This is the direction in which the reconstruction is
verified once the field isomorphism has been constructed.
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open IsDedekindDomain

variable {K₁ K₂ L₁ L₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field L₁] [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K₁ L₁] [Algebra K₂ L₂]
  [FiniteDimensional K₁ L₁] [FiniteDimensional K₂ L₂] [IsGalois K₁ L₁] [IsGalois K₂ L₂]

/-- **The local correspondence at the primes.**  An isomorphism of Galois groups `φ` matches the
Frobenius elements at the prime `P₁` of `L₁` with those at the prime `P₂` of `L₂`.

This is the precise form of the local correspondence of Neukirch–Uchida (12.1.9) used by the
reconstruction step; it is *not* implied by `φ` mapping the decomposition group of `P₁` onto that
of `P₂`, because a group isomorphism may permute the Frobenius elements inside a decomposition
group (e.g. an inert prime `P` in `ℚ(ζ₃)/ℚ` has decomposition group all of `ℤ/3` and its unique
Frobenius is one specific element, while the inversion automorphism of `ℤ/3` maps it to the other
non-trivial element). -/
def MatchesFrobeniusAt (φ : Gal(L₁/K₁) ≃* Gal(L₂/K₂)) (P₁ : PrimeIdeal L₁)
    (P₂ : PrimeIdeal L₂) : Prop :=
  ∀ τ : Gal(L₁/K₁), IsFrobAt P₁ τ ↔ IsFrobAt P₂ (φ τ)

/-- **Frobenius is preserved by an isomorphism matching the local correspondence.** -/
theorem IsFrobAt.map_of_matchesFrobeniusAt {φ : Gal(L₁/K₁) ≃* Gal(L₂/K₂)}
    {P₁ : PrimeIdeal L₁} {P₂ : PrimeIdeal L₂} (h : MatchesFrobeniusAt φ P₁ P₂)
    {σ : Gal(L₁/K₁)} (hσ : IsFrobAt P₁ σ) : IsFrobAt P₂ (φ σ) :=
  (h σ).mp hσ

end NK.Chebotarev
