/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Satisfiability audit of the ramification chapter

Four inputs of this development have already been found false or empty (the Lubin–Tate datum, the
trivial-coefficient `LocalH2Input`, the Hasse principle for odd `p`, and
`NK.LocalAnabelian.HasPTorsionAbelianization`); this file records the audit that the present
chapter adds no fifth.

The audit has three parts.

1. **The definitions are not vacuous.**  `NK.Ramification.ramificationSubgroup A 0` is the
   inertia subgroup `A.inertiaSubgroup K` of the decomposition subgroup
   (`ramificationSubgroup_zero`), and for the local Galois group `Gal(L_q/K_Q)` of a finite Galois
   extension of number fields the filtration has non-trivial, computable content: its zeroth
   subgroup has cardinality the ramification index `e(q|Q)`
   (`NK.Ramification.natCard_ramificationSubgroup_zero_adicCompletion`) and it becomes trivial
   at some finite level (`NK.Ramification.exists_adicRamificationSubgroup_eq_bot`,
   `NK.Ramification.exists_ramificationSubgroup_eq_bot`).

2. **The new named proposition has an inhabited hypothesis and a satisfiable conclusion.**
   `NK.Ramification.NeukirchKennzeichnung` is stated for a pair of `p`-adic fields `κ`, `N` and a
   *continuous* isomorphism `Gal(κ̄/κ) ≃* Gal(κ̄'/N)`; the diagonal instance `N = κ`, `Φ = 1` is
   continuous and its conclusion is the field isomorphism `κ ≃+* κ` produced below
   (`nonempty_bot_ringEquiv_adicCompletion`).  In particular the proposition is not of the shape
   `∀ …, False`.

3. **No new input is introduced.**  `NeukirchKennzeichnung` is *equivalent* to the input already on
   disk, `NK.LocalStructure.LocalFieldFromFiniteExtensionLattice` — the equivalence is proved in
   `Submission/Work/Ramification/Headline.lean` — and the latter is in turn equivalent to the
   workspace's data-free form `NK.LocalStructure.LocalNUExistence` modulo the existence of
   lattice correspondences.  The chapter therefore neither strengthens nor weakens the catalogue;
   it *reduces* it, by showing that the data-heavy hypothesis `FiniteExtensionCorrespondence` can
   be replaced by the classical continuity condition, and by naming what is missing
   (the group-theoretic definability of the higher ramification filtration) explicitly.

The honest residual-input account, with the references, is in
`Submission/Work/Ramification/README.md`.
-/
import Submission.NK.Ramification.Headline
import Submission.NK.Ramification.Determined
import Submission.NK.Ramification.Adic
import Submission.NK.Ramification.natCard_ramificationSubgroup_zero_adicCompletion
import Submission.NK.Ramification.exists_adicRamificationSubgroup_eq_bot
import Submission.NK.Ramification.lowerIndex_le_zero
import Submission.NK.Ramification.upperRamificationSubgroup_antitone
import Submission.NK.Ramification.herbrand_strictMono
import Submission.NK.Ramification.herbrandInv_le_iff
import Submission.NK.Ramification.lowerBreak_iff_lowerIndex_lt
import Submission.NK.Ramification.ramificationSubgroup_map_conj
import Submission.NK.Ramification.continuous_of_finiteExtensionCorrespondence
import Submission.NK.Ramification.RamificationKennzeichnung
import Submission.NK.Ramification.Tower
import Submission.NK.Ramification.hasseArf_iff_dvd
import Submission.NK.Ramification.hasseArf_of_subsingleton
import Submission.NK.Ramification.hasseArf_of_one_eq_zero_and_three_eq_bot
import Submission.NK.Ramification.herbrandRat_eq_id_of_forall_eq_bot
import Submission.NK.Ramification.herbrandMultiplicativity_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.Ramification

universe u

/-- **The trivial instance of the hypothesis of `NeukirchKennzeichnung` has a true conclusion.**
Taking `N = ⊥` (so that `↥⊥` is the copy of the base field `𝔭.adicCompletion K` inside the
separable closure `K'`), the field isomorphism is the identity — which witnesses both that the
hypothesis class of the new named proposition is inhabited and that its conclusion is not
vacuous. -/
theorem nonempty_bot_ringEquiv_adicCompletion (K : Type u) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] :
    Nonempty ((⊥ : IntermediateField (𝔭.adicCompletion K) K') ≃+* 𝔭.adicCompletion K) :=
  ⟨(IntermediateField.botEquiv (𝔭.adicCompletion K) K').toRingEquiv⟩

/-- **Audit 3, restated**: the new named proposition is equivalent to the input already on disk, so
nothing new is being assumed. -/
theorem audit_no_new_input :
    NeukirchKennzeichnung.{u} ↔
      NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} :=
  neukirchKennzeichnung_iff_localFieldFromFiniteExtensionLattice'

/-- **Audit 1, restated for the local field of the workspace**: the zeroth ramification subgroup of
`Gal(L_q/K_Q)` has cardinality the ramification index `e(q|Q)`, so the filtration is not
identically trivial in the ramified case. -/
theorem audit_natCard_zero_adicCompletion {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ↥(ramificationSubgroup (K := Q.adicCompletion K) (q.adicCompletionIntegers L) 0) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
  natCard_ramificationSubgroup_zero_adicCompletion Q q hq

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## Audit of `HasseArf` and `HerbrandMultiplicativity`

These two named propositions of the chapter are stated for the general case and proved only in
special cases, so they need an audit of their own: their hypothesis classes must be inhabited and
their conclusions realised, or they would be a fifth defective input.
-/

/-- **Audit of `HasseArf`**: the proposition is *satisfied* — for a trivial decomposition subgroup
(equivalently for any extension with trivial filtration, e.g. an unramified one) the only lower
break is `0` and `φ(0) = 0`.  So `HasseArf` is not an empty or unsatisfiable predicate. -/
theorem audit_hasseArf (A : ValuationSubring L) [Subsingleton ↥(A.decompositionSubgroup K)]
    [Finite ↥(A.decompositionSubgroup K)] :
    NK.Ramification.HasseArf (K := K) A :=
  hasseArf_of_subsingleton A

/-- **Audit of `HasseArf`, the divisibility form**: the general statement has been reduced to a
single divisibility condition at the lower breaks, which is the classical form, so the residual
input is exactly Hasse's theorem and not a formal artefact. -/
theorem audit_hasseArf_iff_dvd (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] :
    NK.Ramification.HasseArf (K := K) A ↔
      ∀ i : ℕ, NK.Ramification.LowerBreak (K := K) A i →
        NK.Ramification.lowerIndex (K := K) A 0 ∣
          ∑ j ∈ Finset.range i, NK.Ramification.lowerIndex (K := K) A j :=
  hasseArf_iff_dvd A

/-- **Audit of `HerbrandMultiplicativity`**: the rational Herbrand function used in its statement
is tied to `herbrand` on the integers (`herbrandRat_natCast`) and degenerates to the identity for an
everywhere-trivial filtration — the mechanism by which the degenerate cases (`M` trivial over `K`,
or `M = L`) of the multiplicativity hold. -/
theorem audit_herbrandRat_trivial (A : ValuationSubring L)
    (h : ∀ i : ℕ, NK.Ramification.ramificationSubgroup (K := K) A i = ⊥) (u : ℚ) :
    NK.Ramification.herbrandRat (K := K) A u = u :=
  herbrandRat_eq_id_of_forall_eq_bot A h u

/-- **Audit of `HerbrandMultiplicativity`**: the proposition is *satisfied* in the degenerate case
`M = ⊥` (equivalently `M/K` trivial), where the identity `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` reduces to
`φ_{L/K} = φ_{L/K}`. -/
theorem audit_herbrandMultiplicativity_bot (A : ValuationSubring L) :
    NK.Ramification.HerbrandMultiplicativity (K := K) A ⊥ :=
  herbrandMultiplicativity_bot A

end NK.Ramification
