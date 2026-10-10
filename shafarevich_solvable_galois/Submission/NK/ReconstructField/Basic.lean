import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ReconstructField/` — producing the field isomorphism `σ` of CoNF XII §12.2

This is the `NK.ReconstructField` chapter of the Neukirch–Uchida development: the *reconstruction*
of the field isomorphism `σ : K₂' ≃+* K₁'` from the local correspondence `(A)` of CoNF (12.1.9) and
the local Frobenius correspondence `(B)` of Shimizu's Lemma 2.1.5 / `NK.LocalTame`.

The setting is that of the theorem: `K₁`, `K₂` number fields with separable closures `K₁'`, `K₂'`,
and `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` a homeomorphic isomorphism of absolute Galois groups.

## The interface

* **(A)** `NK.Reconstruct.LocalCorrespondence ϕ` (sibling area `Submission/Work/Reconstruct/`):
  the σ-free local correspondence of CoNF (12.1.9) — the Galois-equivariant bijection `placeMap` of
  the place systems, compatible with `ϕ` on decomposition groups (`map_decomp`), together with the
  induced bijection `primeMap` of the finite primes and the arithmetic data (`residueChar`,
  `localDegree`).  It is produced from `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`
  (`Submission/Work/BrauerHasse/`) plus the local structure theory (`Submission/Work/LocalInputs/`).

* **(B)** `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a`: the σ-free local Frobenius
  correspondence (sibling area `Submission/Work/LocalTame/`): an element of `D_A` is a Frobenius
  element at the place `A` if and only if its image under `ϕ` is a Frobenius element at the
  corresponding place `placeMap A`, at every finite level.

* **(C)** `RealizedByBaseIsomorphism a` (this file): the *reconstruction input*, stated without
  asserting the existence of `σ` — see the docstring below.  It is the "local correspondence is
  realised by a field isomorphism" statement in the precisely-isolated form in which it is needed;
  constructing it is Neukirch's CoNF §12.2 / Shimizu §4 (Theorems 4.0–4.3), and this file's main
  theorem (`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius`) shows that it is the
  *only* remaining input: everything else — the level agreement, the Frobenius correspondence and
  the induced group isomorphism — is proved here from `(A)`, `(B)` and it.

The point of the formulation of `(C)` is that it *does not take `σ` as a hypothesis*: it asserts the
existence of a **base-field** isomorphism `τ : K₁ ≃+* K₂` together with a Galois twist `h`, and the
realizing isomorphism is the (provably existing, `NK.ReconstructField.liftBase`) lift of `τ`; the
hypothesis is a condition on the pair `(τ, h)`, not the assertion of a field isomorphism of the
separable closures.
-/

namespace NK.ReconstructField

open IsDedekindDomain

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **A prime of `K` splits completely in `L`**: the number of primes of `𝓞 L` above `p` is the
degree `[L : K]`, i.e. every prime above `p` is unramified of residue degree one.

This is the predicate used by the density theorem
`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`. -/
def SplitsCompletely (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
    [Algebra K L] (p : NK.Chebotarev.PrimeIdeal K) : Prop :=
  (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L

/-- **The prime correspondence of `ϕ` is realized by the ring isomorphism `σ`** (input (C) in the
σ-based form): the place of `K₂'` corresponding to `A` under `ϕ` is the preimage of `A` under `σ`.
Equivalently (by rigidity of decomposition groups) the conjugation by `σ` has the same effect as `ϕ`
on every decomposition group — but the form below is the one used by the reconstruction. -/
def RealizesPlaceCorrespondence {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (σ : K₂' ≃+* K₁') : Prop :=
  ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
    (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1

/-- **The level correspondence realized by `σ`** (a synonym of `NK.Reconstruct.AgreesOnLevels`,
recorded here so that the reconstruction interface is self-contained): the image of the level `L`
of `K₂'` under `σ` is the level of `K₁'` corresponding to `L` under `ϕ`. -/
abbrev RealizesLevelCorrespondence {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (σ : K₂' ≃+* K₁') (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') σ) : Prop :=
  NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ

end NK.ReconstructField
