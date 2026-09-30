import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.PiS.basepointHomog
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.StemsB.PiMap
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area BASEPT: `π₆(S³,x) ≃* π₆(S³,s3)` for every `x : S³`

Reflection of `ℝ⁴` in the hyperplane orthogonal to `x - s3` is a linear isometry equivalence
sending `x` to `s3` (`Work.PiS.reflectionSphere`); it restricts to a homeomorphism `Φ` of the
sphere with `Φ x = s3` (`Work.PiS.sphereIsometryHomeomorph`), hence to a homotopy equivalence.
`Work.Stems.mulEquiv_of_homotopyEquiv` then gives a *group* isomorphism
`π₆(S³,x) ≃* π₆(S³, Φ x)`, and the base point `Φ x` is transported to `s3` along the equality
`Φ x = s3` (`Work.StemsB.homotopyGroupCast`).
-/

set_option synthInstance.maxHeartbeats 400000

namespace Work.Pi6

theorem basepointMulEquiv : Work.Pi6.BasepointMulEquiv := by
  intro x
  -- the reflection in the hyperplane orthogonal to `x - s3`
  obtain ⟨Φ, hΦ⟩ := Work.PiS.sphereIsometryHomeomorph 3
    (((ℝ ∙ ((x : EuclideanSpace ℝ (Fin 4)) - (s3 : EuclideanSpace ℝ (Fin 4))))ᗮ).reflection)
  -- it carries `x` to the chosen base point `s3`
  have hx : Φ x = s3 :=
    Subtype.ext (by rw [hΦ]; exact Work.PiS.reflectionSphere 3 x s3)
  -- a homotopy equivalence induces an isomorphism of homotopy groups
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin 6) Φ.toHomotopyEquiv x
  have h' : Φ.toHomotopyEquiv.toFun x = s3 := by
    rw [Homeomorph.coe_toHomotopyEquiv]
    exact hx
  exact ⟨e.trans (Work.StemsB.homotopyGroupCast h' 5)⟩

end Work.Pi6
