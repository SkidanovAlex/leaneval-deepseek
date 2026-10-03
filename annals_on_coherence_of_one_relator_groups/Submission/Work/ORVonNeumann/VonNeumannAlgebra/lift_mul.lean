import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra

namespace Work.ORVonNeumann.VonNeumannAlgebra

/-- The linear extension `D.lift : ℂ[G] → N(G)` of the regular representation agrees with
`MonoidAlgebra.lift`, and is therefore multiplicative. -/
theorem lift_mul {G : Type*} [Group G] (D : Work.ORVonNeumann.GroupVonNeumannAlgebra G) (f g : MonoidAlgebra ℂ G) : D.lift (f * g) = D.lift f * D.lift g := by
  have h : D.lift = ⇑(MonoidAlgebra.lift ℂ D.N G D.ρ) := by
    funext x
    simp only [Work.ORVonNeumann.GroupVonNeumannAlgebra.lift, MonoidAlgebra.lift_apply]
  rw [h, map_mul]

end Work.ORVonNeumann.VonNeumannAlgebra
