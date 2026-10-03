import Submission.Work.ORLyndon.CLDirect.lyndonIndependence_of_clData
import Submission.Work.ORLyndon.CLDirect.nonempty_clData

/-!
# `Work.ORLyndon.lyndon_independence_of_pow`

The requested statement (kept verbatim below): for `r = u ^ l` with `1 ≤ l` and `u` not a proper
power, the vectors `g • (∂r/∂x)_x` attached to group elements `g` in pairwise distinct
`⟨presentRho r u⟩`-cosets are `K`-linearly independent — the module form of the Cohen--Lyndon
theorem.

## Proof

The proof is the Cohen--Lyndon route of `Submission/Work/ORLyndon/CLDirect/` (design document
`Submission/Work/ORLyndon/CASE2INPUT_LEAD.md`):

* `Work.ORLyndon.CLDirect.nonempty_clData` — N4's Cohen--Lyndon basis
  (`Work.ORLocInd.FKSKernel.cohenLyndonBasis`), packaged as `CLData u`: an isomorphism
  `e : F(F(X)/⟪u⟫) ≃* ⟪u⟫` with `e (of q) = s q * u * (s q)⁻¹` for a transversal `s`;
* `Work.ORLyndon.CLDirect.lyndonIndependence_of_clData` — the assembly: the character `clChi`
  (order of `u` in `G` is `l`), the crossed homomorphism `clDelta` on `F(F(X)/⟪u⟫)` and its
  transport `clPhi` to `⟪u⟫`, the Fox-kernel (Magnus embedding) lemma
  `Work.ORLyndon.CLDirect.foxKernel_vanish`, and the coefficient count
  `Work.ORLyndon.CLDirect.coeffs_zero_of_sum_mul_normElem` on the disjoint cosets of `⟨u⟩`.

This supersedes the earlier (conditional) reduction of `powDefs.lean`/`CLAssembly.lean` to the
Magnus-step input, which is no longer needed.  The unconditional consequences are in
`Submission/Work/ORLyndon/lyndonIdentity_of_pow.lean`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

theorem lyndon_independence_of_pow {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) :
    Work.ORLyndon.LyndonIndependence K r u := by
  subst hpow
  exact Work.ORLyndon.CLDirect.lyndonIndependence_of_clData
    (Classical.choice (Work.ORLyndon.CLDirect.nonempty_clData u hpp)) l hpos

end Work.ORLyndon
