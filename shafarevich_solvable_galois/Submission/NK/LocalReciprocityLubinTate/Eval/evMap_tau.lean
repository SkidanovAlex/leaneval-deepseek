import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Eval

universe u

/-- The evaluation `evMap x : 𝒪[F][T]/(f^{(n)}(T)) → AlgebraicClosure F` attached to a torsion point
`x ∈ Λ_n` sends the class `τ` of `T` to `x`. -/
theorem evMap_tau {F : Type u} [Field F] [ValuativeRel F]
    (π : ↥(ValuativeRel.valuation F).integer) (q n : ℕ) (hq : 2 ≤ q)
    (x : AlgebraicClosure F)
    (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n) :
    NK.LocalReciprocityLubinTate.Eval.evMap π q n hq x hx
      (NK.LocalReciprocityLubinTate.Eval.LTtorsionRing.tau π q n) = x := by
  exact AdjoinRoot.lift_root
    (f := NK.LocalReciprocityLubinTate.LTpolyIter π q n) _

end NK.LocalReciprocityLubinTate.Eval
