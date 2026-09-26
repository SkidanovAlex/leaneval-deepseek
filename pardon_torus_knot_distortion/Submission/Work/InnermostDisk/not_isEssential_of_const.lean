import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.not_isEssential_of_section

namespace Work.InnermostDisk

open Work.CoreTopology

/-- **The constant curve of the torus is inessential.**

A curve which is constantly equal to a point `x ∈ F = P.carrier` is null-homotopic in `F`,
so its winding vector vanishes and it is not essential.  Concretely, choosing parameters
`(a, b)` with `P.psi a b = x`, the set `{x}` carries the constant continuous section
`y ↦ (a, b)` of the parametrisation `P.psi`, so `not_isEssential_of_section` applies. -/
theorem not_isEssential_of_const (P : Work.CoreTopology.ParamTorus)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) (hx : x ∈ P.carrier) :
    ¬ Work.CoreTopology.IsEssential P (Work.InnermostDisk.constCurve P x hx) := by
  obtain ⟨a, b, hab⟩ := (P.mem_carrier_iff x).mp hx
  refine not_isEssential_of_section (s := {x})
    (⟨fun _ => (a, b), continuous_const⟩) ?_ (fun t => ?_)
  · intro y
    show P.psi a b = (y : LeanEval.KnotTheory.PardonDistortion.R3)
    rw [hab, Set.mem_singleton_iff.mp y.2]
  · simp

end Work.InnermostDisk
