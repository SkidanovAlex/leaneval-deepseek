/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# The general Čebotarev density theorem

This chapter proves the general Čebotarev density theorem in the form in which the
Neukirch–Uchida development consumes it, namely the statement
`NK.WeakNU.ChebotarevFrobeniusInput`:  for every finite Galois extension `N/ℚ` of number fields,
every `σ : Gal(N/ℚ)` and every finite set `T` of rational primes there are a rational prime
`p ∉ T`, unramified in `N`, and a prime `P` of `𝓞 N` above `p` with `IsFrobAt P σ`.

## The route taken here

Čebotarev's theorem is proved by combining two inputs that are available in this workspace:

* the **abelian case** `NK.Chebotarev.AbelianChebotarevOfLFunctions` (discharged from the analytic
  input of Hecke `L`-functions, itself discharged from the global Artin reciprocity law of class
  field theory in `Submission/Work/HeckeL/`):  for an abelian extension `L/K` of number fields and
  `σ : Gal(L/K)`, the set of primes of `K` whose Frobenius is `σ` has Dirichlet density
  `1/|Gal(L/K)|`;
* the **transfer step** (`NK.ChebotarevGeneral.DeuringTransfer`, after Deuring 1937): the *cyclic
  case implies the general case*.  For `N/K` finite Galois, `σ ∈ Gal(N/K)`, `H = ⟨σ⟩` and
  `M = N^H` the extension `N/M` is cyclic, so the abelian case gives the density `1/ord(σ)` of the
  primes of `M` at which `σ` is a Frobenius element of `N/M`.  The transfer step converts this into
  the density of the primes of `K` at which `σ` is a Frobenius element of `N/K`.

## Main definitions

* `NK.ChebotarevGeneral.frobSet` — the set of primes of `K` at which `σ` is a Frobenius element;
* `NK.ChebotarevGeneral.IsFrobClassAt`, `frobClassSet` — the same for a conjugacy class;
* `NK.ChebotarevGeneral.frobDensity` — the density `1/|C_G(σ)| = |cl(σ)|/|G|` predicted by
  Čebotarev for the Frobenius class of `σ`;
* `NK.ChebotarevGeneral.frobSetSub` — the Frobenius set of an intermediate field, i.e. of the
  extension `N/M` for `M ⊆ N`;
* `NK.ChebotarevGeneral.AbelianChebotarevDensity` — the abelian case in density form;
* `NK.ChebotarevGeneral.ChebotarevDensity` — the general density statement;
* `NK.ChebotarevGeneral.DeuringTransfer` — the transfer step;
* `NK.ChebotarevGeneral.HasFrobeniusDensity` — a "positive density" form of the statement, from
  which `NK.WeakNU.ChebotarevFrobeniusInput` follows.
-/

import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.Density
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.Chebotarev.GalRestrictCompat
import Submission.NK.Chebotarev.IsFrobAtConj
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.Chebotarev.IsFrobAtStabilizes
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.WeakNU.Defs
import Submission.NeukirchUchida.Local.DecompositionGroup
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_le_finrank
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.NumberTheory.NumberField.absNorm_eq_pow_inertiaDeg_of_liesOver

namespace NK.ChebotarevGeneral

set_option linter.unusedSectionVars false

noncomputable section

open NK.Chebotarev

/-! ## The Frobenius set of an element and of a conjugacy class -/

section FrobeniusSet

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N]

/-- **The Frobenius set of `σ`**:  the set of primes of `K` at which `σ` is a Frobenius element of
the extension `N/K`, i.e. the set of primes `p` for which some prime `P` of `𝓞 N` above `p` satisfies
`NK.Chebotarev.IsFrobAt P σ`.

This is the set whose Dirichlet density Čebotarev's theorem computes. -/
def frobSet (σ : Gal(N/K)) : Set (PrimeIdeal K) :=
  {p | IsFrobAtPrime (K := K) (L := N) p σ}

@[simp]
theorem mem_frobSet {σ : Gal(N/K)} {p : PrimeIdeal K} :
    p ∈ frobSet (K := K) (N := N) σ ↔ IsFrobAtPrime (K := K) (L := N) p σ := Iff.rfl

/-- **The conjugacy class of `σ`.** -/
def conjClass (σ : Gal(N/K)) : Set (Gal(N/K)) := {τ | IsConj σ τ}

@[simp]
theorem mem_conjClass {σ τ : Gal(N/K)} : τ ∈ conjClass σ ↔ IsConj σ τ := Iff.rfl

/-- **The Frobenius class at a prime.**  `C` is the Frobenius class at `p` if some element of `C` is
a Frobenius element at some prime of `𝓞 N` above `p`.

For an unramified prime `p` the Frobenius elements at the primes above `p` form exactly one
conjugacy class, so this is a genuine class-valued Frobenius; for a ramified prime the predicate is
to be read as a formal extension of the definition. -/
def IsFrobClassAt (p : PrimeIdeal K) (C : Set (Gal(N/K))) : Prop :=
  ∃ σ ∈ C, IsFrobAtPrime (K := K) (L := N) p σ

/-- **The Frobenius set of a conjugacy class.** -/
def frobClassSet (C : Set (Gal(N/K))) : Set (PrimeIdeal K) :=
  {p | IsFrobClassAt (K := K) (N := N) p C}

@[simp]
theorem mem_frobClassSet {C : Set (Gal(N/K))} {p : PrimeIdeal K} :
    p ∈ frobClassSet (K := K) (N := N) C ↔ IsFrobClassAt (K := K) (N := N) p C := Iff.rfl

/-- The cardinality of the conjugacy class of `σ`. -/
def conjClassCard (σ : Gal(N/K)) : ℕ := Nat.card (conjClass σ)

/-- **The density predicted by Čebotarev's theorem for the Frobenius class of `σ`**, namely
`|cl(σ)| / |G| = 1 / |C_G(σ)|`. -/
def frobDensity (σ : Gal(N/K)) : ℝ :=
  1 / (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ)

/-- `σ` is unramified at `p`, i.e. every prime of `𝓞 N` above `p` has ramification index one. -/
def IsUnramifiedAt (p : PrimeIdeal K) : Prop :=
  ∀ P : PrimeIdeal N, P.asIdeal.LiesOver p.asIdeal →
    P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1

end FrobeniusSet

/-! ## The Frobenius set of an intermediate field -/

section SubSet

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **The Frobenius set of the intermediate field `M`**:  the set of primes of `M` at which the
element of `Gal(N/M)` induced by `σ ∈ Gal(N/K)` (assumed to fix `M` pointwise) is a Frobenius
element of the extension `N/M`.

This is the set to which the *abelian* case of Čebotarev is applied in the transfer step:  for
`M = N^H` with `H = ⟨σ⟩` the extension `N/M` is cyclic, and `frobSetSub M σ _` is the set whose
density `1/|H|` the abelian case provides. -/
def frobSetSub (M : IntermediateField K N) (σ : Gal(N/K)) (hσ : σ ∈ M.fixingSubgroup) :
    Set (PrimeIdeal ↥M) :=
  {q | IsFrobAtPrime (K := ↥M) (L := N) q (M.fixingSubgroupEquiv ⟨σ, hσ⟩)}

@[simp]
theorem mem_frobSetSub {M : IntermediateField K N} {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    {q : PrimeIdeal ↥M} :
    q ∈ frobSetSub (K := K) (N := N) M σ hσ ↔
      IsFrobAtPrime (K := ↥M) (L := N) q (M.fixingSubgroupEquiv ⟨σ, hσ⟩) := Iff.rfl

end SubSet

/-! ## The statement of Čebotarev's theorem -/

/-- **The abelian case of Čebotarev's density theorem**, in density form and over an arbitrary
number field base:  if `N/K` is a finite Galois extension of number fields with commutative Galois
group and `σ : Gal(N/K)`, then the primes of `K` whose Frobenius is `σ` have Dirichlet density
`1/|Gal(N/K)|`.

This is `NK.Chebotarev.AbelianChebotarevOfLFunctions` (modulo the Hecke `L`-function input
`NK.Chebotarev.AbelianLFunctions`), packaged as a single statement so that the reduction of the
general case to it can be stated without mentioning `L`-functions. -/
def AbelianChebotarevDensity : Prop :=
  ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N],
    (∀ a b : Gal(N/K), a * b = b * a) → ∀ σ : Gal(N/K),
      NumberField.Set.HasDirichletDensity (frobSet (K := K) (N := N) σ)
        (1 / (Nat.card (Gal(N/K)) : ℝ))

/-- **The general Čebotarev density theorem.**  For a finite Galois extension `N/K` of number
fields and `σ : Gal(N/K)`, the set of primes of `K` whose Frobenius class is the class of `σ` has
Dirichlet density `|cl(σ)|/|G|`.

The statement is given in the equivalent form `1/|C_G(σ)|` for the density (see
`NK.ChebotarevGeneral.frobDensity`), which is the form in which the cyclic case occurs. -/
def ChebotarevDensity : Prop :=
  ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] (σ : Gal(N/K)),
    NumberField.Set.HasDirichletDensity (frobSet (K := K) (N := N) σ)
      (frobDensity (K := K) (N := N) σ)

/-- **Čebotarev's theorem in existence form**:  in a finite Galois extension `N/K` of number fields,
every element of the Galois group is a Frobenius element at some prime of `K`.  This is the form of
Čebotarev's theorem that is needed for the Neukirch–Uchida input
`NK.WeakNU.ChebotarevFrobeniusInput`, and it follows from the transfer step below. -/
def ChebotarevInfinite : Prop :=
  ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] (σ : Gal(N/K)),
    (frobSet (K := K) (N := N) σ).Infinite

/-- **The transfer step of the reduction of Čebotarev's theorem to its cyclic case** (Deuring).

Let `N/K` be a finite Galois extension of number fields and `σ : Gal(N/K)`; put `H = ⟨σ⟩` and
`M = N^H`, so that the extension `N/M` is cyclic of degree `ord(σ)` and `σ ∈ Gal(N/M)`.  The abelian
case of Čebotarev provides the density `1/ord(σ)` of the set of primes of `M` at which `σ` is a
Frobenius element of `N/M` (`NK.ChebotarevGeneral.frobSetSub`).  The statement below is that this
implies the density `1/|C_G(σ)|` of the primes of `K` at which `σ` is a Frobenius element of
`N/K`. -/
def DeuringTransfer : Prop :=
  ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] (σ : Gal(N/K)),
    NumberField.Set.HasDirichletDensity
        (frobSetSub (K := K) (N := N) (IntermediateField.fixedField (Subgroup.zpowers σ)) σ
          (by rw [IntermediateField.fixingSubgroup_fixedField]
              exact Subgroup.mem_zpowers σ))
        (1 / (Nat.card (Subgroup.zpowers σ) : ℝ)) →
      NumberField.Set.HasDirichletDensity (frobSet (K := K) (N := N) σ)
        (frobDensity (K := K) (N := N) σ)

end

end NK.ChebotarevGeneral
