import Mathlib
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.FuncExt
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.negAlgEquiv_transX
import Submission.Work.MotC2.negAlgEquiv_transY

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- `[-1] · τ_Q = τ_{-Q} · [-1]`: negation conjugates the translation action to its inverse
(`τ : E(L) → Aut_L(L(E))` is a `[-1]`-twisted homomorphism).

Both sides are `L`-algebra automorphisms of `L(E)`, so by
`Work.MotC2.funcAlgEquiv_ext_genX_genY` it suffices to compare their values on `x = genX E` and
`y = genY E`; using `Work.MotC2.negAlgEquiv_transX`, `Work.MotC2.negAlgEquiv_transY`,
`Work.MotC2.transAlgEquiv_apply`, `Work.MotC2.phi_genX`, `Work.MotC2.phi_genY`,
`Work.MotC2.negAlgEquiv_genX` and `Work.MotC2.negAlgEquiv_genY`, both sides are
`transX E (-Q)` and `-transY E (-Q) - a₁ · transX E (-Q) - a₃` respectively. -/
theorem negAlgEquiv_mul_transAlgEquiv {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) :
    Work.MotC2.negAlgEquiv E * Work.MotC2.transAlgEquiv E Q =
      Work.MotC2.transAlgEquiv E (-Q) * Work.MotC2.negAlgEquiv E := by
  refine funcAlgEquiv_ext_genX_genY E _ _ ?_ ?_
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, transAlgEquiv_apply, phi_genX,
      negAlgEquiv_transX, negAlgEquiv_genX, transAlgEquiv_apply, phi_genX]
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, transAlgEquiv_apply, phi_genY,
      negAlgEquiv_transY, negAlgEquiv_genY, map_sub, map_sub, map_mul, AlgEquiv.commutes,
      AlgEquiv.commutes, map_neg, transAlgEquiv_apply, phi_genY, transAlgEquiv_apply, phi_genX]

end Work.MotC2
