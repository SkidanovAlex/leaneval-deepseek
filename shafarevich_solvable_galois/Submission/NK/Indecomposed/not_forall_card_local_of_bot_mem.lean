/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cardinality hypothesis of the rank count is never satisfied by *all* local groups

`NK.Indecomposed.RankData` (and the rank count of `Submission/Work/HasseTwist/`) is fed the
hypothesis that every local group `V ∈ NK.HasseTwist.localGroupSubgroupsOver H 𝔭` has twisted
cohomology of cardinality `≥ p`,

`hloc : ∀ V ∈ localGroupSubgroupsOver H 𝔭, p ≤ Nat.card (H2Twist p V)`.

That hypothesis is *stronger than what the rank count needs*: it can only hold if `⊥` is **not** a
local group over `𝔭`.  Indeed the trivial group is one of the local groups exactly when the prime is
decomposed, and the twisted cohomology of the trivial group is a point
(`NK.Indecomposed.subsingleton_h2Twist_bot`), so `Nat.card (H2Twist p ⊥) ≤ 1 < p` for a prime `p`.

This file records that observation in the form in which the assembly uses it: membership of `⊥` in
the set of local groups *refutes* the all-groups cardinality hypothesis.  Consequently the criterion
`NK.Indecomposed.localDecompositionCriterion_of_twistedHasse_allLocals` may be applied with the
literal request hypothesis: the hypothesis is inconsistent precisely in the situation (a decomposed
prime) where nothing has to be proved.

## Contents

* `NK.Indecomposed.not_forall_card_local_of_bot_mem` — the statement.
-/

import Mathlib
import Submission.NK.Indecomposed.Defs
import Submission.NK.Indecomposed.subsingleton_h2Twist_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.Indecomposed

/-- **The point `H2Twist p ⊥` has cardinality at most one.**  (Stated here for an arbitrary
subsingleton type, since `Nat.card` of a subsingleton is `≤ 1` with no finiteness hypothesis: it is
`0` when the type is infinite and `1` when it is a nonempty finite subsingleton.) -/
private lemma nat_card_le_one_of_subsingleton (X : Type u) [Subsingleton X] :
    Nat.card X ≤ 1 := by
  by_cases hfin : Finite X
  · exact @Finite.card_le_one_iff_subsingleton X hfin |>.mpr inferInstance
  · haveI : Infinite X := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le 1

/-- **The all-groups cardinality hypothesis fails as soon as the prime is decomposed.**

If `⊥` is a local group of `H` over `𝔭` — i.e. if there is a place `A` of `K'` over `𝔭` with
`H ⊓ D_A = ⊥`, the prime being decomposed for the intermediate field of `H` — then the cardinality
hypothesis `p ≤ Nat.card (H2Twist p V)` cannot hold for *every* local group over `𝔭`: it fails at
`V = ⊥`, because `H2Twist p ⊥` is a point
(`NK.Indecomposed.subsingleton_h2Twist_bot`) while `p` is a prime, hence `p ≥ 2`. -/
theorem not_forall_card_local_of_bot_mem {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hbot : (⊥ : Subgroup Gal(K'/K)) ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭) :
    ¬ (∀ V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
        p ≤ Nat.card (NK.BrauerTwist.H2Twist (K := K) (K' := K') p V)) := by
  intro h
  have hcard :
      Nat.card (NK.BrauerTwist.H2Twist (K := K) (K' := K') p
        (⊥ : Subgroup Gal(K'/K))) ≤ 1 := by
    haveI : Subsingleton (NK.BrauerTwist.H2Twist (K := K) (K' := K') p
        (⊥ : Subgroup Gal(K'/K))) :=
      subsingleton_h2Twist_bot (K := K) (K' := K') p
    exact nat_card_le_one_of_subsingleton _
  have hbot_card := h ⊥ hbot
  have hp2 : 2 ≤ p := hp.two_le
  omega

end NK.Indecomposed
