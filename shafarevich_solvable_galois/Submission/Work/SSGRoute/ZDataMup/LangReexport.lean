import Mathlib
import Submission.NK.CFTLib.ARLTransfer.kernelLe_of_auxField
import Submission.NK.CFTLib.ARL.auxField_exists_B
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.NUV2.ARL.Gap.langCyclicRelIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbolKillsPrincipal_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Re-export of the (clean) Lang-era conductor machinery

This module only re-exports, for use by the lemmas in `Submission/Work/`, the clean modules of the
Lang-era (Artin's lemma) conductor machinery, which live under `Submission/NK/`.

* `NK.CFTLib.ARLTransfer.kernelLe_of_auxField` — Lang's transfer
  `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)`;
* `NK.CFTLib.ARL.auxField_exists_B` — Artin's lemma's auxiliary-field hypothesis holds for every
  modulus `m > 0`;
* `NK.NUV2.ARL.Gap.langCyclicRelIndex` — the cyclic norm index inequality
  `[L:K] ≤ [I(m) : P(m)·𝔑(m)]` (for admissible `m` containing the ramified primes);
* `NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe` — the reverse inequality;
* `NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime`, `normRayLeKer` — the two inputs of
  the index computation;
* `NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex` — the final
  assembly turning the containment plus the index computation into `artinKillsPrincipal`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section
