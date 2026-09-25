/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The surjectivity companion of Neukirch's rank count

This module formalises the second half of the local-global arithmetic input of block (i) of the
Neukirch–Uchida development: the **surjectivity of the localisation at a prime**, which together
with the local rank computations yields Neukirch's "the prime is indecomposed" conclusion — the
`eq:NeukirchH2modifiedsurj` of A. Ivanov, arXiv:1309.2801, i.e. NSW (9.2.1), and the
`NK.LocalDecomposition.IndecomposedPrime` of the sibling chapter, in the coefficient-correct
(`μ_p`-twisted) form.

## What is formalised

Fix a number field `K`, a separable closure `K'`, and a finite prime `𝔭` of `K`.

* `NK.HasseTwist.PlacesOverPrime K K' 𝔭` — the places of `K'` over `𝔭` (the valuation subrings of
  `K'` whose restriction to `K` is `𝒪_𝔭`);
* `NK.HasseTwist.localGroupSubgroupsOver U 𝔭` — the set of **local groups** of a closed subgroup
  `U ≤ Gal(K'/K)` at the places over `𝔭`, i.e. the subgroups `U ⊓ D_A` for `A` over `𝔭`.  It is the
  *quotient* of the set of places over `𝔭` by the relation "same local group"; classically its
  cardinality is that of the set of primes of the fixed field `K'^U` above `𝔭`, and Neukirch's
  conclusion is that this set is a singleton;
* `NK.HasseTwist.H2Twist.resTo` — the restriction `H²(U, μ_p) → H²(U ⊓ D_A, μ_p)`, and
  `NK.HasseTwist.localisationTo` — the product of these restrictions over the places over `𝔭`;
* **`NK.HasseTwist.NeukirchH2modifiedsurj`** — the *named classical input*: for every closed
  `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` (`κ` a `p`-adic field) and every finite prime `𝔭`, the
  product of the restrictions to the local groups over `𝔭` is surjective.  This is the shape of the
  sequence `H²(H', μ_{p^∞}) → ⊕_{𝔭' ∈ S_𝔭(M')} H²(D_{𝔭'}, μ_{p^∞}) → 0` of
  Neukirch, Invent. Math. **6** (1969), Theorem 1 (proof), quoted by Ivanov, arXiv:1309.2801, proof
  of Proposition `classobstrdec` (equation `eq:NeukirchH2modifiedsurj`), whose reference is
  Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (9.2.1);
* **`NK.HasseTwist.indecomposedAt_of_surjective`** — the *rank count itself*, proved: if the
  localisation is surjective, `|H²(U, μ_p)| = p` and every local group `V` over `𝔭` satisfies
  `|H²(V, μ_p)| ≥ p`, then all the local groups of `U` over `𝔭` coincide.  The two cardinality
  hypotheses are the local computations of local class field theory (`H²(G_κ, μ_p) ≅ Z/p`,
  NSW (7.1.7), and the non-vanishing for the local groups, NSW (7.1.8)(i),(ii), as used by Ivanov);
  they are hypotheses of the rank count, not universal claims about all subgroups of `U` — see
  `README.md` §5;
* **`NK.HasseTwist.le_stabSubgroup_of_indecomposedAt`** and
  **`NK.HasseTwist.le_stabSubgroup_of_input`** — the group-theoretic form of Neukirch's conclusion
  `H₀ = D_𝔭 ∩ H`: every local group over `𝔭` lies in the decomposition group of every place over
  `𝔭`;
* **`NK.HasseTwist.exists_loc_ne_zero_and_indecomposed`** — the *composite* statement of block (i):
  every non-zero class of `H²(H, μ_p)` has a non-zero local component at a place over a prime `𝔭`,
  and that prime is indecomposed for `H`.

## Relation to `NK.LocalDecomposition.IndecomposedPrime`

`NK.LocalDecomposition.IndecomposedPrime` is the same classical input in the
*trivial*-coefficient vocabulary (`NK.BrauerHasse.H2Profinite`); the statement below is its
coefficient-correct (`μ_p`) counterpart, and the two differ in exactly the way documented in
`Submission/Work/BrauerTwist/README.md` (the trivial-coefficient form is false for odd `p` when
`μ_p ⊄ κ`).  The rank count proved here is the exact content of the "counting the coranks" step of
Neukirch's proof; see `Submission/Work/HasseTwist/README.md` §§5–6 for the discussion of the shape
of the input and of its satisfiability.
-/

import Submission.NK.HasseTwist.Restrict
import Submission.NK.HasseTwist.subsingleton_of_surjective_prod
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## The places over a fixed finite prime -/

/-- **The places of `K'` over a fixed finite prime `𝔭` of `K`**: the valuation subrings of `K'`
whose restriction to `K` is the valuation ring `𝒪_𝔭`. -/
abbrev PlacesOverPrime (K K' : Type u) [Field K] [NumberField K] [Field K'] [Algebra K K']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type u :=
  {A : ValuationSubring K' //
    A.comap (algebraMap K K') = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭}

/-- The prime of `K` below a place of `K'` over a finite prime of `K`. -/
noncomputable def primeUnder (A : OverFinitePrime K K') :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  Classical.choose (NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K')
    A.1 A.2)

/-- The defining property of `primeUnder`. -/
lemma primeUnder_spec (A : OverFinitePrime K K') :
    A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K (primeUnder A) :=
  Classical.choose_spec (NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K')
    A.1 A.2)

/-- The valuation ring of a finite prime of a number field is not the whole field.
(Re-proved here from `Valuation.valuationSubring_eq_top_iff`; this is the same argument as
`Submission.NeukirchUchida.Local.valuationSubringAtPrime_ne_top`.) -/
lemma isDedekindDomain_valuationSubringAtPrime_ne_top
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ≠ ⊤ := by
  intro h
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.valuationSubring_eq_top_iff] at h
  exact h inferInstance

/-- A place of `K'` over the finite prime `𝔭` of `K` is a place over a finite prime of `K`. -/
noncomputable def PlacesOverPrime.toOverFinitePrime
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (A : PlacesOverPrime K K' 𝔭) : OverFinitePrime K K' :=
  ⟨A.1, by rw [A.2]; exact isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭⟩

/-! ## The local groups over a prime -/

/-- **The set of local groups of `U` at the places over `𝔭`**: the subgroups `U ⊓ D_A` of the
decomposition groups of the places `A` of `K'` over `𝔭`.  This is the index set of Neukirch's rank
count (classically: the set of primes of the fixed field of `U` above `𝔭`). -/
def localGroupSubgroupsOver (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set (Subgroup Gal(K'/K)) :=
  Set.range fun A : PlacesOverPrime K K' 𝔭 => U ⊓ stabSubgroup A.1

/-- A local group over `𝔭` is contained in `U`. -/
lemma le_of_mem_localGroupSubgroupsOver {U : Subgroup Gal(K'/K)} {𝔭 : _}
    {V : Subgroup Gal(K'/K)} (h : V ∈ localGroupSubgroupsOver (K := K) (K' := K') U 𝔭) :
    V ≤ U := by
  obtain ⟨A, hA⟩ := h
  rw [← hA]
  exact inf_le_left

/-- Membership in `localGroupSubgroupsOver`, unwound. -/
lemma mem_localGroupSubgroupsOver_iff {U : Subgroup Gal(K'/K)} {𝔭 : _}
    {V : Subgroup Gal(K'/K)} :
    V ∈ localGroupSubgroupsOver (K := K) (K' := K') U 𝔭 ↔
      ∃ A : PlacesOverPrime K K' 𝔭, U ⊓ stabSubgroup A.1 = V :=
  Iff.rfl

/-- **The restriction to a local group**: for `V` a local group of `U` at a place over `𝔭` the
restriction map `H²(U, μ_p) → H²(V, μ_p)` on the twisted profinite cohomology. -/
noncomputable def H2Twist.resTo (p : ℕ) {U : Subgroup Gal(K'/K)} {𝔭 : _}
    {V : Subgroup Gal(K'/K)} (h : V ∈ localGroupSubgroupsOver (K := K) (K' := K') U 𝔭) :
    H2Twist p U → H2Twist p V :=
  H2Twist.res p (le_of_mem_localGroupSubgroupsOver h)

/-! ## The inputs -/

/-- **The surjectivity of the localisation at a prime (`eq:NeukirchH2modifiedsurj`).**

For every closed subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` (`κ` a `p`-adic field) and every
finite prime `𝔭` of `K`, the product of the restriction maps to the local groups of `U` at the places
over `𝔭` is **surjective**:

`H²(U, μ_p) ↠ ∏_{V ∈ localGroupSubgroupsOver U 𝔭} H²(V, μ_p)`.

This is the classical input of Neukirch's rank count: for an open subgroup `H' ≤ H` of a subgroup
`H` of `p`-decomposition type, the localisation `H²(H', μ_{p^∞}) → ⊕_{𝔭' ∈ S_𝔭(M')} H²(D_{𝔭'}, μ_{p^∞})
→ 0` is exact (Neukirch, Invent. Math. **6** (1969), Theorem 1; Ivanov, arXiv:1309.2801, equation
`eq:NeukirchH2modifiedsurj`; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (9.2.1)).

Classically it is the *cokernel* form of the global Hasse principle: the sum of the local invariants
of a Brauer class is zero, so a prescribed family of local invariants at the primes over a *single*
prime `𝔭` can be realised by a global class after compensating at other primes.  The labelling by
`κ` is essential, exactly as for `NK.HasseTwist.Sha2Input` (see `README.md` §§4–6). -/
def NeukirchH2modifiedsurj (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      Function.Surjective (fun x : H2Twist p U =>
        fun (V : ↥(localGroupSubgroupsOver (K := K) (K' := K') U 𝔭)) =>
          H2Twist.resTo p V.2 x)

/-- **The surjectivity of the localisation at a prime, in the form in which Neukirch's argument uses
it**: only at a prime `𝔭` carrying a *non-zero local component* (the prime found in Neukirch's
argument via the vanishing of the limiting Sha², `NK.HasseTwist.exists_loc_ne_zero`).  This is the
weaker reading of `NK.HasseTwist.NeukirchH2modifiedsurj`; it is the hypothesis actually needed by
the rank count, and it is the one used in `NK.HasseTwist.exists_loc_ne_zero_and_indecomposed`. -/
def NeukirchH2modifiedsurjAt (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (∃ (A : PlacesOverPrime K K' 𝔭) (x : H2Twist p U),
        H2Twist.loc p U x A.toOverFinitePrime ≠ 0) →
      Function.Surjective (fun x : H2Twist p U =>
        fun (V : ↥(localGroupSubgroupsOver (K := K) (K' := K') U 𝔭)) =>
          H2Twist.resTo p V.2 x)

/-- The unconditional form of the input implies the form used by Neukirch's argument. -/
theorem NeukirchH2modifiedsurjAt_of (p : ℕ) (h : NeukirchH2modifiedsurj p K K' κ κ') :
    NeukirchH2modifiedsurjAt p K K' κ κ' :=
  fun U hU hκ 𝔭 _ => h U hU hκ 𝔭

/-- **"The prime `𝔭` is indecomposed for `U`"**, in the group-theoretic form of Neukirch's
conclusion: all the local groups of `U` at the places over `𝔭` coincide.  Classically this says that
`U` is contained in the decomposition group `D_A` of every place `A` over `𝔭` (take the local group
`U ⊓ D_A = U` of the place at which the localisation is non-zero — see
`NK.HasseTwist.le_stabSubgroup_of_indecomposedAt`), i.e. that the prime does not decompose in the
extension `K'/K'^U`. -/
def IndecomposedAt (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  ∀ V W : ↥(localGroupSubgroupsOver (K := K) (K' := K') U 𝔭), V = W

/-! ## The rank count -/

section RankCount

variable {U : Subgroup Gal(K'/K)}
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}

/-- The product of the restriction maps to the local groups of `U` at the places over `𝔭`. -/
noncomputable def localisationTo (p : ℕ) (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    H2Twist p U → ∀ V : ↥(localGroupSubgroupsOver (K := K) (K' := K') U 𝔭), H2Twist p V.1 :=
  fun x V => H2Twist.resTo p V.2 x

/-- **Neukirch's rank count.**  If the localisation to the local groups over `𝔭` is surjective, the
source `H²(U, μ_p)` has `p` elements, and every local group `V` over `𝔭` has `|H²(V, μ_p)| ≥ p`,
then all the local groups of `U` over `𝔭` coincide.

This is the "counting the coranks" step of Neukirch's proof of Theorem 1 (Invent. Math. **6** (1969);
Ivanov, arXiv:1309.2801, proof of Proposition `classobstrdec`): the corank of the source is `1` and
each summand of the target has corank `≥ 1`, so the surjectivity forces the target to have exactly one
summand.  The two cardinality hypotheses are the local computations of local class field theory:
`H²(G_κ, μ_p) ≅ Z/p` for a `p`-adic field `κ` (NSW (7.1.7)) and the non-vanishing
`H²(V, μ_p) ≠ 0` for the local groups `V = U ⊓ D_A` (NSW (7.1.8)(i),(ii), as used by Ivanov); they
hold in the situation of Neukirch's argument, where all the local groups occurring are non-trivial.
See `Submission/Work/HasseTwist/README.md` §5 for the discussion — in particular, the cardinality
hypothesis is *not* a universal statement about all subgroups `V ≤ U`: for a decomposition group `U`
the local group of a *distinct* place over the same prime is trivial (the FKS theorem,
`NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne`), and the hypothesis correctly fails there. -/
theorem indecomposedAt_of_surjective (p : ℕ) (hp : p.Prime)
    (hcard : Nat.card (H2Twist p U) = p)
    (hloc : ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') U 𝔭,
      p ≤ Nat.card (H2Twist p V))
    (hsurj : Function.Surjective (localisationTo (K := K) (K' := K') p U 𝔭)) :
    IndecomposedAt (K := K) (K' := K') U 𝔭 :=
  subsingleton_of_surjective_prod p hp hcard (fun V => hloc V.1 V.2)
    (localisationTo (K := K) (K' := K') p U 𝔭) hsurj

/-- **The rank count from the input catalogue.** -/
theorem indecomposedAt_of_input (p : ℕ) (h : NeukirchH2modifiedsurj p K K' κ κ')
    (hp : p.Prime)
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hκ : Nonempty (U ≃* Gal(κ'/κ)))
    (hcard : Nat.card (H2Twist p U) = p)
    (hloc : ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') U 𝔭,
      p ≤ Nat.card (H2Twist p V)) :
    IndecomposedAt (K := K) (K' := K') U 𝔭 :=
  indecomposedAt_of_surjective (K := K) (K' := K') p hp hcard hloc (h U hU hκ 𝔭)

/-- **The group-theoretic form of "the prime `𝔭` is indecomposed for `U`"**: every local group of
`U` at a place over `𝔭` is contained in the decomposition group of every place over `𝔭`. -/
theorem le_stabSubgroup_of_indecomposedAt (h : IndecomposedAt (K := K) (K' := K') U 𝔭)
    (A A' : PlacesOverPrime K K' 𝔭) :
    U ⊓ stabSubgroup A.1 ≤ stabSubgroup A'.1 := by
  have h1 : U ⊓ stabSubgroup A.1 = U ⊓ stabSubgroup A'.1 :=
    Subtype.ext_iff.mp (h ⟨U ⊓ stabSubgroup A.1, ⟨A, rfl⟩⟩ ⟨U ⊓ stabSubgroup A'.1, ⟨A', rfl⟩⟩)
  rw [h1]
  exact inf_le_right

/-- **The rank count from the guarded form of the input.** -/
theorem indecomposedAt_of_inputAt (p : ℕ) (h : NeukirchH2modifiedsurjAt p K K' κ κ')
    (hp : p.Prime) (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hκ : Nonempty (U ≃* Gal(κ'/κ)))
    (hguard : ∃ (A : PlacesOverPrime K K' 𝔭) (x : H2Twist p U),
      H2Twist.loc p U x A.toOverFinitePrime ≠ 0)
    (hcard : Nat.card (H2Twist p U) = p)
    (hloc : ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') U 𝔭,
      p ≤ Nat.card (H2Twist p V)) :
    IndecomposedAt (K := K) (K' := K') U 𝔭 :=
  indecomposedAt_of_surjective (K := K) (K' := K') p hp hcard hloc
    (h U hU hκ 𝔭 hguard)

/-- **The rank count, in the form consumed by Neukirch's Theorem 1.**  Under the input catalogue,
every local group of `H` at a place over `𝔭` is contained in the decomposition group of every place
over `𝔭` — which is `H ≤ D_{A'}` for the local group of the place carrying a non-zero local
component. -/
theorem le_stabSubgroup_of_input (p : ℕ) (h : NeukirchH2modifiedsurj p K K' κ κ')
    (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hcard : Nat.card (H2Twist p H) = p)
    (hloc : ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
      p ≤ Nat.card (H2Twist p V)) :
    ∀ A A' : PlacesOverPrime K K' 𝔭, H ⊓ stabSubgroup A.1 ≤ stabSubgroup A'.1 :=
  fun A A' =>
    le_stabSubgroup_of_indecomposedAt
      (indecomposedAt_of_input (K := K) (K' := K') (κ := κ) (κ' := κ') p h hp H hH hκ
        hcard hloc) A A'

end RankCount

/-! ## The conclusion in the shape of `NK.LocalDecomposition.IndecomposedPrime` -/

section Consumers

variable {U : Subgroup Gal(K'/K)}
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}

/-- **The rank count from the guarded form of the input, in group-theoretic form.** -/
theorem le_stabSubgroup_of_inputAt (p : ℕ) (h : NeukirchH2modifiedsurjAt p K K' κ κ')
    (hp : p.Prime) (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hguard : ∃ (A : PlacesOverPrime K K' 𝔭) (x : H2Twist p H),
      H2Twist.loc p H x A.toOverFinitePrime ≠ 0)
    (hcard : Nat.card (H2Twist p H) = p)
    (hloc : ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
      p ≤ Nat.card (H2Twist p V)) :
    ∀ A A' : PlacesOverPrime K K' 𝔭, H ⊓ stabSubgroup A.1 ≤ stabSubgroup A'.1 :=
  fun A A' => le_stabSubgroup_of_indecomposedAt
    (indecomposedAt_of_inputAt (K := K) (K' := K') (κ := κ) (κ' := κ') (𝔭 := 𝔭) p h hp H hH hκ
      hguard hcard hloc) A A'

/-- **Neukirch's conclusion in the existential shape of `NK.LocalDecomposition.IndecomposedPrime`**:
there is a local group `H₀ ≤ H` of `H` which is contained in the decomposition group of a place over
a finite prime of `K`.  (The classical refinement `0 < H₀.relIndex H` — the openness of the local
group in `H` — is *not* part of this statement; it is the input `IndecomposedPrime` of the sibling
chapter, and follows there from the localisation output together with Neukirch's Korollar 1.) -/
theorem exists_le_stabSubgroup_of_input (p : ℕ) (h : NeukirchH2modifiedsurj p K K' κ κ')
    (hp : p.Prime) (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hcard : Nat.card (H2Twist p H) = p)
    (hloc : ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
      p ≤ Nat.card (H2Twist p V)) (A : PlacesOverPrime K K' 𝔭) :
    ∃ (H₀ : Subgroup Gal(K'/K)) (A' : ValuationSubring K'),
      H₀ ≤ H ∧ A'.comap (algebraMap K K') ≠ ⊤ ∧
        H₀ ≤ MulAction.stabilizer Gal(K'/K) A' :=
  ⟨H ⊓ stabSubgroup A.1, A.1, inf_le_left,
    by rw [A.2]; exact isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭,
    le_stabSubgroup_of_input (K := K) (K' := K') (κ := κ) (κ' := κ') p h hp H hH hκ 𝔭
      hcard hloc A A⟩

end Consumers

/-! ## The composite statement of block (i) -/

/-- **The composite local-global statement of block (i), with the rank count.**

Under the input catalogue of this chapter — the `μ_p`-twisted Hasse principle `Sha2Input`, the local
Brauer input `LocalH2Input` and the surjectivity `NeukirchH2modifiedsurj`, together with the two local
rank computations (`|H²(H, μ_p)| = p` and `|H²(V, μ_p)| ≥ p` for the local groups `V`) — every
non-zero class `x` of `H²(H, μ_p)` has a non-zero local component at a place `A` over a finite prime
`𝔭`, and that prime is *indecomposed* for `H`: every local group of `H` at a place over `𝔭` lies in
the decomposition group of every place over `𝔭`.

The first conjunct is `NK.HasseTwist.exists_loc_ne_zero` (the Hasse principle `sha2Vanishing`
together with the local Brauer input); the second is Neukirch's rank count
(`NK.HasseTwist.le_stabSubgroup_of_input`), i.e. the group-theoretic content of
`NK.LocalDecomposition.IndecomposedPrime`. -/
theorem exists_loc_ne_zero_and_indecomposed (p : ℕ)
    (hSha : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (_hLoc : LocalH2Input (K := K) (K' := K') p κ κ')
    (hSurj : NeukirchH2modifiedsurjAt p K K' κ κ')
    (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Twist p H} (hx : x ≠ 0)
    (hcard : Nat.card (H2Twist p H) = p)
    (hloc : ∀ (A : OverFinitePrime K K') (V : Subgroup Gal(K'/K)),
      V ∈ localGroupSubgroupsOver (K := K) (K' := K') H (primeUnder A) →
        p ≤ Nat.card (H2Twist p V)) :
    ∃ (A : OverFinitePrime K K'),
      H2Twist.loc p H x A ≠ 0 ∧
        ∀ A' A'' : PlacesOverPrime K K' (primeUnder A),
          H ⊓ stabSubgroup A'.1 ≤ stabSubgroup A''.1 := by
  obtain ⟨A, hA⟩ := NK.BrauerTwist.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Vanishing (K := K) (K' := K') (κ := κ) (κ' := κ') p hSha) H hH hκ hx
  refine ⟨A, hA, ?_⟩
  have hEq : PlacesOverPrime.toOverFinitePrime (K := K) (K' := K') (𝔭 := primeUnder A)
      ⟨A.1, primeUnder_spec A⟩ = A := Subtype.ext rfl
  have hguard : ∃ (A' : PlacesOverPrime K K' (primeUnder A)) (y : H2Twist p H),
      H2Twist.loc p H y A'.toOverFinitePrime ≠ 0 :=
    ⟨⟨A.1, primeUnder_spec A⟩, x, by rw [hEq]; exact hA⟩
  exact fun A' A'' => le_stabSubgroup_of_indecomposedAt
    (indecomposedAt_of_inputAt (K := K) (K' := K') (κ := κ) (κ' := κ') (𝔭 := primeUnder A)
      p hSurj hp H hH hκ hguard hcard (fun V hV => hloc A V hV)) A' A''

end NK.HasseTwist
