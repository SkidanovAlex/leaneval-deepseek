import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# RETRACTED STATEMENT (session 4): the one-dimensional `z`-data with a confinement level

**This file records a mis-stated lemma.**  The theorem which stood here -- the `μ_p`/`p = 2`
`z`-data of Schmidt--Wingberg §4 with two extra clauses, namely *confinement* ("every good place at
which `z` is ramified has all its conjugates split completely in a level `M`") and *killing* ("`z`
vanishes on the local groups of the conjugates of a prescribed set `T''` of good places") -- was
reviewed by four reviewers ("looks correct as stated" for its shape) and then shown to be
**false as stated** by two provers, independently, for the two parities of `p`:

* the prover of the odd-`p` copy
  (`Submission/Work/SSGRoute/z_data_mup_level_proof.lean`) exhibited the obstruction through the
  Poitou--Tate realisation criterion: the hypothesis `hyunr` (which forbids ramification of `y`
  only at places that are *unramified* in `M`) leaves `y` free to ramify at `M`-ramified places
  outside `cs(S) ∪ cs(T'')`, and the conclusion then forces any admissible `z` to be unramified
  there, i.e. to realise the local datum of `y` with its ramification confined to a set disjoint
  from the ramification of `y` itself.  By the reciprocity of local invariants this fails as soon
  as `y` is ramified at such a place, because the local Tate pairing of the ramified part of `y`
  against the Selmer dual does not vanish.  (The paper's Theorem 13 avoids this by assuming `(H1)`
  -- `y` unramified at `P ∉ T(K)` -- and by taking the *ramification of the level* into the set
  `T`; the formalised hypotheses were strictly weaker.)
* the prover of the `p = 2` copy
  (`Submission/Work/SSGRoute/z_data_two_level_proof.lean`) identified the missing hypothesis as the
  link `M ≤ Λ` between the level of the confinement clause and the auxiliary field, and proved in
  Lean (`Work.SSGRoute.z_data_two_level_of_le`, axiom-clean) that **with `M ≤ Λ` the statement is
  trivial**, the witness being `z := y` extended by `0` off `G_K`: every good place is then
  `M`-split, so the confinement clause is automatic, and `hyunr`/`hyT''` make the sharpened clause
  (b) of `HasZData` vacuous.

**Consequences for the node** (see `ZConstruction/ZDataInduction.lean`).

* The *level`↦`field* direction that Schmidt--Wingberg's induction actually uses is the **change of
  the auxiliary field `Λ`**, not of an independent confinement level: the one-dimensional input is
  applied at the *enlarged* pair `(Λ·L, S)`, where `L` is the level of the first summand.  The rung
  that makes this usable is proved in `ZConstruction/ZDataInduction.lean`:
  `Work.SSGRoute.hasZData_of_le_level` (`HasZData K Λ' S y z → Λ ≤ Λ' → HasZData K Λ S y z`).
* The triviality above shows that at the enlarged pair the only input needed for the `finrank ≤ 1`
  case is the *trivial* one, which needs no arithmetic; the genuine arithmetic content of the node
  is therefore concentrated in the case `finrank ≥ 2` *and* in the transfer of `y`'s ramification
  from the places of `cs(S) ∩ ...` to the "new" primes of §4.
-/

namespace Work.SSGRoute

end Work.SSGRoute
