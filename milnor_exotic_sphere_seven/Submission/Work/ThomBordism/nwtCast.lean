import Mathlib
import Submission.Work.ThomBordism.nwtAux
import Submission.Work.Whitney.ChernRelDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- The degree cast `4 * 2 = 8` is the identity. -/
theorem eqRec_four_two (h : 4 * 2 = 8) (x : Work.Thom.Coh ℤ (4 * 2) B) :
    (h ▸ x : Work.Thom.Coh ℤ 8 B) = x := by
  have h1 : h = rfl := Subsingleton.elim _ _
  rw [h1]

/-- The degree cast `4 + 4 = 8` is the identity. -/
theorem eqRec_four_four (h : 4 + 4 = 8)
    (x : (Work.Cohomology.cochainC ℤ (Work.Whitney.ssB B)).homology (4 + 4)) :
    (h ▸ x : Work.Thom.Coh ℤ 8 B) = x := by
  have h1 : h = rfl := Subsingleton.elim _ _
  rw [h1]

/-- **The casted cup product is the graded-commutative `Work.Whitney.cupChern`** (the degrees
`4, 4` are even, so the Koszul sign is trivial). -/
theorem cupH'_cast_eq_cupChern_swap (h : 4 + 4 = 8)
    (a b : (Work.Cohomology.cochainC ℤ (Work.Whitney.ssB B)).homology 4) :
    (h ▸ Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 4 4 a b : Work.Thom.Coh ℤ 8 B)
      = Work.Whitney.cupChern 2 2 b a := by
  have h1 : h = rfl := Subsingleton.elim _ _
  have h2 : ((Nat.mul_add 2 2 2).symm : 2 * 2 + 2 * 2 = 2 * (2 + 2)) = rfl :=
    Subsingleton.elim _ _
  rw [h1, Work.Whitney.ChernRel.cupChern_comm 2 2 b a, Work.Whitney.cohTransport_eq_self,
    Work.Whitney.cupChern_def, h2, Work.Thom.cohTransport_rfl]

end

end Work.ThomBordism
