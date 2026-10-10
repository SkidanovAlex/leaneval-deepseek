import Mathlib
import Submission.Work.Totaro.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- A partial isomorphism whose source is all of `X` has no exceptional divisor: every point is an
isomorphism point, since the partial isomorphism itself witnesses `IsIsoAt`. -/
lemma exDiv_eq_empty_of_source_eq_top {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (i : X.PartialIso Y) (h : i.source = ⊤) :
    exDiv i.toBirationalMap = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  exact hx.2 ⟨i, by rw [h]; trivial, (PartialIso.toBirationalMap_hom i).symm⟩

/-- An isomorphism `X ≅ Y` over the base yields a pseudo-isomorphism `X ⤏ Y`: every point of `X` is an isomorphism point, so `Work.Totaro.exDiv` is empty in both directions.  This is the base case of the pseudo-isomorphism calculus of the Totaro area (paper `thm:BurtCY` clause (1)). -/
theorem isPseudoIso_of_isoOver {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) :
    Work.Totaro.IsPseudoIso ((AlgebraicGeometry.Scheme.PartialIso.ofIso e).toBirationalMap) := by
  refine ⟨exDiv_eq_empty_of_source_eq_top (PartialIso.ofIso e) (PartialIso.ofIso_source e), ?_⟩
  show exDiv ((PartialIso.ofIso e).symm.toBirationalMap) = ∅
  exact exDiv_eq_empty_of_source_eq_top (PartialIso.ofIso e).symm (by simp [PartialIso.ofIso])

end Work.Totaro
