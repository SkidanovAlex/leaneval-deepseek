/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Satisfiability, non-vacuity and universe audit of the input catalogue

The audit duty of this area is to check that the classical inputs of `Defs.lean` are *satisfiable*
and *non-vacuous*, and that no hypothesis is introduced which cannot hold at a concrete instance.
This module records what can be *proved* about that:

1. **The `(A)`-part of the catalogue is implied by the rank data of the framework.**  If the rank
   data `NK.Indecomposed.RankData p K K' κ κ'` is instantiable (as it is classically: it is the
   local Brauer computation plus Neukirch's surjectivity), then so are
   `NK.IndecomposedDeep.GlobalBrauerTransport p K K' κ κ'` and
   `NK.IndecomposedDeep.LocalGroupBrauer p K K' κ κ'`.  Hence the two new inputs of `RankData.lean`
   are not stronger than what the framework already assumes, and are satisfiable whenever the rank
   data is.

2. **The finishing step is implied by Neukirch's criterion.**  The on-disk
   `NK.LocalDecomposition.indexOne_of_localDecompositionCriterion` shows that
   `NK.LocalDecomposition.IndexOneOfSelfNormalizing` (the `finishingStep` input) follows from
   Neukirch's criterion together with the local Brauer non-vanishing.  So the input is a
   *consequence* of the classical theorem, not an independent strengthening — modulo the audit
   finding recorded in `Corrected.lean` and `README.md` §6 (the criterion form used on disk is the
   trivial-coefficient one; for `p = 2` the two coefficient modules agree, which is the case of the
   development's `p = 2` route).

3. **`LocalGroupBrauer` is satisfiable and correct as stated**: the restriction to non-trivial local
   groups is *necessary* (the on-disk
   `NK.Indecomposed.not_forall_card_local_of_bot_mem` refutes the unrestricted form as soon as
   `⊥` occurs as a local group, i.e. as soon as the prime is decomposed in `K'/K`).

4. **Universe check.**  All the statements of this chapter are polymorphic in one universe `u`, and
   every field of every structure is at `Type u`; `NK.Indecomposed.RankData.{u}`,
   `NK.Indecomposed.LocalReconstruction.{u}` (and, via (1), the catalogue) are inhabited exactly at
   the universe of the fields.  In particular the chapter fits the endgame, which is
   universe-polymorphic (`Submission/Work/Mine/NeukirchUchidaOfResiduals.lean`).
-/

import Submission.NK.IndecomposedDeep.Endgame

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Auxiliary.**  Two types whose `Nat.card` is the same non-zero natural are in bijection. -/
theorem nonempty_equiv_of_natCard_eq {α β : Type u} {n : ℕ} (hn : n ≠ 0)
    (h1 : Nat.card α = n) (h2 : Nat.card β = n) : Nonempty (α ≃ β) := by
  haveI : Finite α := (Nat.card_ne_zero.mp (by rw [h1]; exact hn)).2
  haveI : Finite β := (Nat.card_ne_zero.mp (by rw [h2]; exact hn)).2
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  refine ⟨Fintype.equivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h1, h2]

/-- **Audit (1), the labelling transport**: the input `GlobalBrauerTransport` is a *consequence* of
the rank data together with the local Brauer computation at the local field.  So it is satisfiable
whenever the rank data is, and it adds no strength to the framework's assumptions. -/
theorem globalBrauerTransport_of_rankData (hrank : NK.Indecomposed.RankData p K K' κ κ')
    (hbr : LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p) :
    GlobalBrauerTransport p K K' κ κ' where
  equiv U hU hκ :=
    nonempty_equiv_of_natCard_eq hrank.hp.ne_zero (hrank.card_global U hU hκ)
      (natCard_H2Twist_top_of_localFieldBrauerCyclic hbr)

/-- **Audit (1), the local groups**: the input `LocalGroupBrauer` is exactly the `card_local` field
of the rank data, so it is satisfiable whenever the rank data is. -/
theorem localGroupBrauer_of_rankData (hrank : NK.Indecomposed.RankData p K K' κ κ') :
    LocalGroupBrauer p K K' κ κ' where
  card_local := hrank.card_local

/-- **Audit (2), the finishing step**: `NK.LocalDecomposition.IndexOneOfSelfNormalizing` follows
from Neukirch's criterion and the local Brauer non-vanishing (the on-disk
`NK.LocalDecomposition.indexOne_of_localDecompositionCriterion`), so it is a consequence of the
classical theorem rather than an independent assumption.  (The criterion used on disk is the
trivial-coefficient one; by `NK.BrauerTwist.muRep_isTrivial_of_isPrimitiveRoot` the two coefficient
modules agree in the regime `ζ_p ∈ κ`, in particular at `p = 2` for every `p`-adic `κ`.) -/
theorem indexOne_of_localDecompositionCriterion
    (hC : NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ')
    (h2 : NK.BrauerHasse.LocalH2Input p K K' κ κ') :
    NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ' :=
  NK.LocalDecomposition.indexOne_of_localDecompositionCriterion (K := K) (K' := K')
    (κ := κ) (κ' := κ') hC h2

/-- **Audit (3): the restriction to the non-trivial local groups is necessary.**

If `⊥` occurs among the local groups of `H` over `𝔭` — which happens exactly when `𝔭` is decomposed
in `K'/K`, and in particular for every decomposition group `H = D_A` over the prime below `A`
(`NK.Indecomposed.mem_localGroupSubgroupsOver_stabSubgroup`) — then the cardinality hypothesis
`p ≤ Nat.card (H2Twist p V)`, imposed on *all* local groups, is refutable.  Consequently the
restricted form used by `LocalGroupBrauer` is the only usable one; the literal unrestricted form
would make the catalogue unsatisfiable. -/
theorem not_forall_card_local_of_bot_mem_localGroup {H : Subgroup Gal(K'/K)}
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hbot : (⊥ : Subgroup Gal(K'/K)) ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭)
    (hp : p.Prime) :
    ¬ (∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
        p ≤ Nat.card (H2Twist p V)) :=
  NK.Indecomposed.not_forall_card_local_of_bot_mem (K := K) (K' := K') p hp H 𝔭 hbot

/-- **Audit (4): the rank data at `p = 2` from the catalogue.**  The `p = 2` route of the
development (`NK.Indecomposed.indecomposedPrime_two_of_rankData`) consumes
`NK.Indecomposed.RankDataTrivial 2 K K' κ κ'`, whose coefficient module is the trivial `ℤ/2`; at
`p = 2` and in characteristic `≠ 2` the cyclotomic twist `μ_2 = {±1}` is the trivial module
(`NK.BrauerTwist.muRep_isTrivial_of_isPrimitiveRoot`), so the two coincide.  The comparison of the
two *colimits* (`H2Twist 2` versus `H2Profinite 2`) is the remaining formalisation gap of that
route; the twisted catalogue of this chapter is what the main route consumes. -/
theorem rankData_two_of_inputs (h : DeepInputs 2 K K' κ κ') :
    NK.Indecomposed.RankData 2 K K' κ κ' :=
  rankData_of_deepInputs h

end NK.IndecomposedDeep
