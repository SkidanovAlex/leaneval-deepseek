/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Submission/Work/HasseTwist/` — the local-global arithmetic input of Neukirch–Uchida in the
coefficient-correct (`μ_p`-twisted) form

Umbrella module: `import Submission.NK.HasseTwist.All` (namespace `NK.HasseTwist`).

This chapter discharges — from a small, labelled, satisfiable catalogue of classical inputs, with
every reduction *proved* — the local-global arithmetic input of block (i) of the Neukirch–Uchida
development:

* **the Hasse principle with cyclotomic coefficients**,
  `NK.HasseTwist.sha2Vanishing : Sha2Input p K K' κ κ' → NK.BrauerTwist.Sha2Vanishing p K K' κ κ'`
  (Hasse–Brauer–Noether `Br(M)[p] ↪ ∏_v Br(M_v)[p]` and its passage to the colimit over the finite
  levels);
* **the surjectivity companion** of Neukirch's rank count,
  `NK.HasseTwist.NeukirchH2modifiedsurj` (the cokernel form of the Hasse principle) together with
  the *proved* rank count `NK.HasseTwist.indecomposedAt_of_surjective` and its consequence
  `NK.HasseTwist.le_stabSubgroup_of_input` — Neukirch's "the prime is indecomposed";
* the corollaries in the vocabulary of the consumer (`NK.BrauerTwist`):
  `NK.HasseTwist.exists_loc_ne_zero`, `NK.HasseTwist.exists_decompositionGroup_of_localGalois`,
  `NK.HasseTwist.fieldAxiom_of_sha2Input`, and the composite
  `NK.HasseTwist.exists_loc_ne_zero_and_indecomposed`.

See `Submission/Work/HasseTwist/README.md` for the full account, including the satisfiability audit
of every input left standing.
-/

import Submission.NK.HasseTwist.Defs
import Submission.NK.HasseTwist.Obstruction
import Submission.NK.HasseTwist.Hasse
import Submission.NK.HasseTwist.Inputs
import Submission.NK.HasseTwist.Main
import Submission.NK.HasseTwist.Consumer
import Submission.NK.HasseTwist.Restrict
import Submission.NK.HasseTwist.Localisation
import Submission.NK.HasseTwist.subsingleton_of_surjective_prod
import Submission.NK.HasseTwist.loc_injective_of_le_stabSubgroup
import Submission.NK.HasseTwist.Inert
import Submission.NK.HasseTwist.exists_finset_levelObstruction
import Submission.NK.HasseTwist.levelRes_injective_of_coprime_index
import Submission.NK.HasseTwist.Pgroup
import Submission.NK.HasseTwist.levelLocVanishing_mono
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
