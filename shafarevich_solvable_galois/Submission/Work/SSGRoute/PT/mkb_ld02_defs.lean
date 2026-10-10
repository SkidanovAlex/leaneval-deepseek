import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.kummerBase_euler_h3loc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared instance plumbing for the `α²`-dévissage at `D_A`

The workspace's decomposition-group actions are *named* definitions
(`Work.SSGRoute.decompDistribMulAction`), not automatically-found instances, so a statement
mentioning e.g. `H³(↥(decomp k A), ·)` or `H²(↥(decomp k A), Additive Ωˣ)` has to say how
`D_A` acts.  This file registers the two actions of `↥(decomp k A)` that the
`mkb_ld02_core_of_h3` assembly needs as found instances:

* `mkbUnitsDecomp` — the action of `↥(decomp k A)` on `Additive Ωˣ`, restricted from the
  action of `Gal(Ω/k)`;
* `mkbConjHomDecomp` — the conjugation action of `↥(decomp k A)` on `Hom_ℤ(N,\bar Ωˣ)`.

Both are *definitionally* the canonical actions; no new structure is introduced.
-/

open Classical

namespace Work.SSGRoute.PT

/-- The canonical `↥(decomp k A)`-action on `Additive Ωˣ` (restriction of the `Gal(Ω/k)`-action
along the subgroup inclusion). -/
noncomputable instance mkbUnitsDecomp (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) [DistribMulAction (Ω ≃ₐ[k] Ω) (Additive (Units Ω))] :
    DistribMulAction ↥(SSGRoute.decomp k A) (Additive (Units Ω)) :=
  DistribMulAction.compHom _ (SSGRoute.decomp k A).subtype

/-- The conjugation action of `↥(decomp k A)` on `Hom_ℤ(N,\bar Ωˣ)` (the action on the source is
supplied by the ambient instance). -/
noncomputable instance mkbConjHomDecomp (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (N : Type) [AddCommGroup N]
    [DistribMulAction ↥(SSGRoute.decomp k A) N]
    [DistribMulAction ↥(SSGRoute.decomp k A) (Additive (Units Ω))] :
    DistribMulAction ↥(SSGRoute.decomp k A) (ConjHom N (Additive (Units Ω))) :=
  inferInstance

end Work.SSGRoute.PT
