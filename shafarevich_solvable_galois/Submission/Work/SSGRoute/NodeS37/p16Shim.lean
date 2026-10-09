import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.Reconstruct.denseChebotarev
import Submission.Work.SSGRoute.SSG8Escape.ChebotarevDensityInput
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import shim for the p. 16 representative normalisation

Re-exports, for `request_lemma`'s `depends_on` (which resolves under `Submission/Work/`):

* `Commons.NumberTheory.NumberField.Completion.placeSmul` (the Galois action on
  `HeightOneSpectrum`, needed to say that a prime is not fixed by an involution);
* `NK.Reconstruct.ChebotarevDensityInput` and the *proved* unconditional instance
  `Work.SSG8Escape.chebotarevDensityInput_general`, together with the existence form
  `Work.SSGRoute.exists_isFrobAtPrime_notMem_density`
  (`Submission/Work/SSGRoute/ssg8Chebotarev.lean`) — the Čebotarev input in the form in which it is
  actually available in this workspace (over an arbitrary number field base, with a finite set of
  primes avoided).
-/
