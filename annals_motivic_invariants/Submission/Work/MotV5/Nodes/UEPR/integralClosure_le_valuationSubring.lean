import Mathlib
import Submission.Work.MotV5.Nodes.UEPR.valuation_le_one_of_isIntegral

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `haveI` below introduces the `IsIntegrallyClosedIn` instance for the valuation subring of `w`;
-- the style linter misreads this as an inlined `have`.
set_option linter.style.haveILetI false

namespace Work.MotV5.Nodes.UEPR

/-- **Integral elements lie in the valuation ring.**

Let `F` be a field with a valuation `v` (finite dimensional hypothesis is not needed), `Ω` a field
extension of `F`, and `w` a valuation of `Ω` whose unit ball contains exactly the elements of the
unit ball of `v` (in the sense of `hsub`).  Then every element of `Ω` which is integral over the
valuation ring of `v` lies in the valuation ring of `w`.

The proof is the standard "a valuation ring is integrally closed": the subring `{y | w y ≤ 1}` is
integrally closed in `Ω` (`ValuationSubring` of a field is integrally closed, transferred to the
`Subring` formulation by `Subring.integralClosure_le_iff`), and the image of the valuation ring of
`v` is contained in it by `hsub`. -/
theorem integralClosure_le_valuationSubring {F Ω Γ : Type*} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F (WithZero (Multiplicative ℤ))) (w : Valuation Ω Γ) (hsub : ∀ x : F, w (algebraMap F Ω x) ≤ 1 ↔ v x ≤ 1) : (integralClosure ↥(v.valuationSubring) Ω).toSubring ≤ w.valuationSubring.toSubring := by
  haveI : IsIntegrallyClosedIn w.valuationSubring.toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn w.valuationSubring Ω)
  rw [Subring.integralClosure_le_iff]
  intro r
  show w (algebraMap ↥(v.valuationSubring) Ω r) ≤ 1
  rw [IsScalarTower.algebraMap_apply ↥(v.valuationSubring) F Ω]
  exact (hsub (r : F)).mpr r.2

end Work.MotV5.Nodes.UEPR
