/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The final assembly: Theorem 1.1 conditional on [JZLA20, Proposition 3.11] alone

This file combines the two halves of the ring half of
`Submission/Work/ORFinal/`:

* the JL §5 flatness input `Work.ORFinal.RealTorInput` is now a **theorem**,
  `Work.ORFinal.realTorInput`: the T7 assembly
  `Work.ORFinal.T7.realTorInput_of_chainInput` applied to the dimension-shifting chain
  `Work.ORFinal.chainInput` (T6, `Work.ORFinal.Chain.chainOfJL52` + `Chain.chainHyp_of_augIdeal`);
* `Work.ORFinal.theorem_1_1_of_prop311` (`Submission/Work/ORFinal/Final.lean`) takes that flatness
  input together with node ORP311's [JZLA20, Proposition 3.11].

Hence the challenge statement

> every one-relator group `G` is coherent, and `K[G]` is coherent for every field `K` of
> characteristic zero,

follows from `[JZLA20, Proposition 3.11]` alone: node N6 is a theorem
(`Work.ORFinal.n6EngineInput`), the group-theoretic nodes are discharged
(`Work.ORFinal.nodeInputs`), the `IsMulTorsionFree` requirement of
`Work.ORAssembly.RingInputs` is not used (`Work.ORFinal.RingDataDiv`), and the whole JL §5 chain
(T2, T4, T5, T6, T7, T7a) is proved in this directory.

## Main results

* `Work.ORFinal.realTorInput : Work.ORFinal.RealTorInput`
* `Work.ORFinal.theorem_1_1_of_prop311_only` — the challenge statement from Proposition 3.11 alone.
-/
import Submission.Work.ORFinal.Final
import Submission.Work.ORFinal.Chain.ChainInput
import Submission.Work.ORFinal.T7.realTorInput_of_chainInput

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORFinal

/-- **The JL §5 flatness input of the ring half is a theorem.**  It is the T7 assembly
(`Work.ORFinal.T7.realTorInput_of_chainInput`, i.e. `Work.ORLyndon.magnus_torTwoVanishes` fed with
`hA`, `hswap` and the chain, at the M1 datum of every finitely generated one-relator presentation
with a real coefficient field) applied to the dimension-shifting chain of JL Lemma 5.2, which is
`Work.ORFinal.chainInput` (T6). -/
theorem realTorInput : RealTorInput :=
  T7.realTorInput_of_chainInput chainInput

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton, conditional on [JZLA20, Proposition 3.11] alone.**

For every one-relator group `G` (in any universe) and every field `K` of characteristic zero,
`G` is coherent and `K[G]` is coherent, assuming only node ORP311's Proposition 3.11 over `ℂ`:
for every countable group `G₀` and every locally indicable `H ≤ G₀` the structure map
`ℂ[H] →+* U(G₀)` into the canonical envelope satisfies `IsHughesFreeEnv`. -/
theorem theorem_1_1_of_prop311_only {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (h311 : ∀ (H : Type) [Group H] [Countable H], Work.ORDivLoc.Prop311OnComplexClosure H)
    (hG : Group.OneRelator G) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) :=
  theorem_1_1_of_prop311 h311 realTorInput hG

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton, conditional on (I4) in the JZLA20 engine's form
alone** (`Work.ORFinal.DivLoc`, at the small universe where the ring half is run).

This is the form in which a caller who has node N6's statement directly — i.e. that the division
closure `D H` of `K[H]` in `U(G)` is a division ring for every locally indicable `H ≤ G` — can use
this directory.  Node ORP311's Proposition 3.11 is the special case
(`Work.ORFinal.hdiv_of_prop311`), which is why `theorem_1_1_of_prop311_only` is stated with it. -/
theorem theorem_1_1_of_hdiv_only {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (hdiv : ∀ (L : Type) [Field L] (H : Type) [Group H] [Countable H] (φK : L →+* ℂ),
      DivLoc L H φK)
    (hG : Group.OneRelator G) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) :=
  theorem_1_1_of_hdiv (fun K instK G instG instC φK => hdiv K G φK) realTorInput hG

/-- **The challenge statement, in the binder order of `Challenge.lean` plus the remaining
input.**

This is `Work.ORFinal.theorem_1_1_of_prop311_only` with the arguments in the order in which the
challenge's `theorem_1_1` takes them (`G`, `K`, `hG`), so that the bridge in `Submission.lean` is
`Work.ORFinal.theorem_1_1_of_prop311_challenge G K hG h311`. -/
theorem theorem_1_1_of_prop311_challenge {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (hG : Group.OneRelator G)
    (h311 : ∀ (H : Type) [Group H] [Countable H], Work.ORDivLoc.Prop311OnComplexClosure H) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) :=
  theorem_1_1_of_prop311_only h311 hG

end Work.ORFinal
