import Mathlib
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Action.Basic

set_option linter.style.haveILetI false

namespace Work.ORBassSerre.Action.Structure

/-- A cocompact action restricted to a finite index subgroup is still cocompact: the `H`-orbits
refine the `G`-orbits, and each `G`-orbit is a union of at most `[G : H]` many `H`-orbits.  This is
Mathlib's `MulAction.finite_quotient_of_finite_quotient_of_finite_quotient`, applied to the vertices
and (via the induced action on `Quiver.Total V`) to the edges. -/
theorem isCocompact_of_finiteIndex {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (H : Subgroup G) [H.FiniteIndex] (hcc : Work.ORBassSerre.IsCocompact G V) :
    Work.ORBassSerre.IsCocompact H V := by
  haveI : Finite (MulAction.orbitRel.Quotient G V) := hcc.1
  haveI : Finite (MulAction.orbitRel.Quotient G (Quiver.Total V)) := hcc.2
  exact ⟨inferInstance, inferInstance⟩

end Work.ORBassSerre.Action.Structure
