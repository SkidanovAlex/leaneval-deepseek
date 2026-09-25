/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local groups over a prime, and Neukirch's surjectivity (NSW (9.2.1))

Umbrella development: `Submission/Work/HassePrinciple/` (README §18).

Neukirch's proof of the local characterisation of decomposition groups
(*Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*, Invent. Math. **6**
(1969), Theorem 1) uses one arithmetic input, which he proves by the *rank count*:

> **(9.2.1)**  for the subgroup `H ≤ G_K` of "`p`-decomposition type", the localisation
> `H²(H, μ_{p^∞}) → ⊕_{𝔭' | 𝔭} H²(D_{𝔭'}, μ_{p^∞}) → 0` is exact, i.e. the localisation to the
> local groups at the primes of the fixed field of `H` above a fixed prime `𝔭` of `K` is
> **surjective** (Neukirch, op. cit., Theorem 1 (proof); Neukirch–Schmidt–Wingberg, *Cohomology of
> Number Fields*, (9.2.1); quoted in this workspace as `NK.HasseTwist.NeukirchH2modifiedsurj`).

This module fixes the vocabulary in which that input is stated for the *trivial* coefficient module
`NK.BrauerHasse.Coeff p = Z/p`, which is the module the chapter's target uses:

* `NK.HassePrinciple.localGroupsOver U 𝔭` — the set of local groups of `U` at the places of `K'`
  over the finite prime `𝔭` of `K`.  Classically this is the set of decomposition groups
  `U ⊓ D_A` as `A` runs over the places over `𝔭`; its cardinality is that of the set of primes of
  the fixed field `K'^U` above `𝔭`, i.e. `[U : U ⊓ D_A]`, so the *index set of the product is
  finite exactly when the prime is indecomposed* — which is the conclusion Neukirch draws from the
  surjectivity by counting ranks.  The product is therefore taken over the **local groups**, not
  over the places of `K'` (of which there are always infinitely many): this is the form of (9.2.1)
  in which it is a statement that can be true.
* `NK.HassePrinciple.localGroupLoc p U 𝔭` — the localisation
  `H²(U, Z/p) → ∏_{V ∈ localGroupsOver U 𝔭} H²(V, Z/p)`, whose surjectivity is (9.2.1).
* `NK.HassePrinciple.localGroupsOver_nonempty` — every finite prime of `K` has at least one place
  of `K'` above it (Chevalley's extension theorem, on disk as
  `Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime`), so the index set
  of the product is never empty.
-/

import Submission.NK.HassePrinciple.RankInput
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local groups of `U` at the places of `K'` over the finite prime `𝔭` of `K`**: the
subgroups `U ⊓ D_A`, as `A` ranges over the places of `K'` over `𝔭`.  Classically its cardinality
is the number of primes of the fixed field `K'^U` above `𝔭`, i.e. `[U : U ⊓ D_A]`; the rank count
of Neukirch's proof of (9.2.1) shows that the localisation `H²(U, Z/p) → ∏_{V ∈ localGroupsOver U 𝔭}
H²(V, Z/p)` can only be surjective if this set is small (a singleton, in the situation of the
input). -/
def localGroupsOver (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set (Subgroup Gal(K'/K)) :=
  Set.range (fun A : PlacesOverPrime K K' 𝔭 => U ⊓ stabSubgroup A.1)

/-- Characterisation of the members of `localGroupsOver`: the subgroups `U ⊓ D_A` for `A` over
`𝔭`. -/
theorem mem_localGroupsOver {U : Subgroup Gal(K'/K)}
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {V : Subgroup Gal(K'/K)} :
    V ∈ localGroupsOver U 𝔭 ↔ ∃ A : PlacesOverPrime K K' 𝔭, U ⊓ stabSubgroup A.1 = V :=
  Iff.rfl

/-- **Every finite prime of a number field has a place of `K'` above it** (Chevalley's theorem for
the valuation ring `𝒪_𝔭`), so the product defining `localGroupLoc` is never indexed by the empty
set. -/
theorem localGroupsOver_nonempty (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (localGroupsOver (K := K) (K' := K') U 𝔭).Nonempty := by
  obtain ⟨A, hA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := K) (K' := K') 𝔭
  exact ⟨U ⊓ stabSubgroup A, ⟨⟨A, hA⟩, rfl⟩⟩

/-- A place of `K'` over `𝔭` realising the local group `V` (chosen classically). -/
noncomputable def localGroupPlace {U : Subgroup Gal(K'/K)}
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (V : ↥(localGroupsOver U 𝔭)) : PlacesOverPrime K K' 𝔭 :=
  Classical.choose V.2

/-- The defining property of `localGroupPlace`: the local group of `U` at that place is `V`. -/
theorem localGroupPlace_spec {U : Subgroup Gal(K'/K)}
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (V : ↥(localGroupsOver U 𝔭)) :
    U ⊓ stabSubgroup (localGroupPlace V).1 = V.1 :=
  Classical.choose_spec V.2

/-- **The localisation to the local groups over `𝔭`**: the product of the restrictions
`H²(U, Z/p) → H²(U ⊓ D_A, Z/p)` over the *local groups* `V = U ⊓ D_A`.  Its surjectivity is
Neukirch's (9.2.1) (NSW (9.2.1)); the rank count of `LocalGroupInput.lean` turns it into the
statement that all the local groups over `𝔭` coincide, hence (with the coincidence theorem
`NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective` for the chosen prime `𝔭` and
FKS) into `U ≤ D_A`. -/
noncomputable def localGroupLoc (p : ℕ) (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    H2Profinite p U → ((V : ↥(localGroupsOver U 𝔭)) → H2Profinite p V.1) :=
  fun x V => cast (congrArg (fun W : Subgroup Gal(K'/K) =>
      H2Profinite (K := K) (K' := K') p W) (localGroupPlace_spec (U := U) V))
    (locAt (K := K) (K' := K') p U (localGroupPlace V).toOverFinitePrime x)

/-- Computation rule for `localGroupLoc`: the `V`-component is the localisation at the place
`localGroupPlace V`, transported along the identification of the local group with `V`. -/
theorem localGroupLoc_apply (p : ℕ) (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : H2Profinite p U) (V : ↥(localGroupsOver U 𝔭)) :
    localGroupLoc (K := K) (K' := K') p U 𝔭 x V =
      cast (congrArg (fun W : Subgroup Gal(K'/K) =>
        H2Profinite (K := K) (K' := K') p W) (localGroupPlace_spec (U := U) V))
        (locAt (K := K) (K' := K') p U (localGroupPlace V).toOverFinitePrime x) := rfl


/-! ## The input: Neukirch's surjectivity (NSW (9.2.1)) and the local computations -/

section Input

variable {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's arithmetic input for the local characterisation of decomposition groups**, in the
form of the *rank count* of his proof of Theorem 1 (Invent. Math. **6** (1969)), for the trivial
coefficient module `Z/p`:

1. `hp` — `p` is a prime.
2. `card_global` — for every closed subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, the group
   `H²(U, Z/p)` has exactly `p` elements.  Classically this is the local computation of local class
   field theory at `κ` (`H²(G_κ, Z/p) ≅ Hom(μ_p(κ), Q/Z)`, which is `0` or `Z/p`), transported along
   the labelling `U ≅ Gal(κ'/κ)`.  It is the only place where the cohomology of `κ` enters, and it
   is the statement owed by the local side (`NK.LocalCFT`).
3. `prime_surj` — **Neukirch's (9.2.1)**: for every such `U` there is a finite prime `𝔭` of `K`
   such that (i) every local group `V = U ⊓ D_A` over `𝔭` has `p ≤ |H²(V, Z/p)|` (the local
   computation at the local groups: each `U ⊓ D_A` is the absolute Galois group of a non-archimedean
   local field, so its `H²(·, Z/p)` is `0` or `Z/p`, and the local groups occurring here are
   constructed from `U ≅ Gal(κ'/κ)` hence are local Galois groups), and (ii) the localisation
   `H²(U, Z/p) → ∏_{V ∈ localGroupsOver U 𝔭} H²(V, Z/p)` to the product over the local groups over
   `𝔭` is **surjective**.

Neukirch's rank count (`NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective`) turns the
surjectivity plus the two cardinality statements into the statement that the local groups over `𝔭`
coincide, i.e. that the prime `𝔭` is *indecomposed*; the reduction to the chapter's Hasse principle
`NK.BrauerHasse.Sha2Vanishing` is `NK.HassePrinciple.rankInput_of_nswsInput`.  **The Hasse
principle — the injectivity of the localisation — is not assumed**: what is assumed is a
*surjectivity* statement (the classical cokernel form of the Hasse principle, i.e. the
Albert–Brauer–Hasse–Noether surjectivity), together with the local computations of local class
field theory.  This is the same input that the sibling chapters quote as
`NK.HasseTwist.NeukirchH2modifiedsurj` (with `μ_p`-coefficients) and as
`NK.LocalDecomposition.IndecomposedPrime` (via (9.2.1)). -/
structure NSWSInput (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- **The local computation of local class field theory at `κ`**, transported along the labelling:
  `|H²(U, Z/p)| = p` for every closed `U ≅ Gal(κ'/κ)`. -/
  card_global : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (H2Profinite p U) = p
  /-- **Neukirch's (9.2.1)** at a prime `𝔭`, together with the local computations at the local
  groups. -/
  prime_surj : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) →
      ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (∀ V ∈ localGroupsOver (K := K) (K' := K') U 𝔭,
          p ≤ Nat.card (H2Profinite (K := K) (K' := K') p V)) ∧
          Function.Surjective (localGroupLoc (K := K) (K' := K') p U 𝔭)

end Input

end NK.HassePrinciple
