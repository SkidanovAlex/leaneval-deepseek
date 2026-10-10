import Mathlib
import Submission.Work.CrauderKatz.Defs
import Submission.Work.CrauderKatz.Affine

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

/-- **A partial isomorphism defined on all of `X` has no exceptional divisors.**  In particular an
actual isomorphism has none, which is what makes the transports of the affine form of the
Crauder–Katz link (`Work.CrauderKatz.AffineKatzLink`, where both transports are identities)
contribute nothing to the invariant: `exDiv` is empty, so `cInv` vanishes by
`Work.LLink.cInv_eq_zero_of_exDiv_eq_empty`. -/
theorem exDiv_toBirationalMap_eq_empty_of_source_eq_top {X Y : AlgebraicGeometry.Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (i : X.PartialIso Y) (h : i.source = ⊤) :
    exDiv (i.toBirationalMap) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨-, hx⟩
  exact hx (isIsoAt_toBirationalMap_of_mem_source i (by rw [h]; trivial))

end Work.CrauderKatz
