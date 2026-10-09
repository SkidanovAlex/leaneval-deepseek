import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- The `SSGRoute` inhomogeneous `2`-cocycle condition (written as `a - b + c - d = 0`) for the
action of `Γ` on `M` pulled back along `act : Γ →* G` is exactly membership in the `2`-cocycles
`Z²(Γ, M)` for the pulled-back action, i.e. the equation
`c (g * h, k) + c (g, h) = act g • c (h, k) + c (g, h * k)`. -/
theorem bridge_isCocycle2_mem_Z2 {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M] [DistribMulAction G M] (act : Γ →* G) (c : Γ × Γ → M) : SSGRoute.IsCocycle2 act (fun g h => c (g, h)) ↔ c ∈ @Work.GroupCohomology.Z2 Γ M _ _ (DistribMulAction.compHom M act) := by
  rw [Work.GroupCohomology.mem_Z2_iff]
  constructor
  · intro hc g h k
    rw [MulAction.compHom_smul_def]
    have H := hc g h k
    have H2 : act g • c (h, k) + c (g, h * k) = c (g * h, k) + c (g, h) := by
      have : act g • c (h, k) + c (g, h * k) - (c (g * h, k) + c (g, h)) = 0 := by
        rw [← H]; abel
      exact sub_eq_zero.mp this
    exact H2.symm
  · intro hZ g h l
    have H := hZ g h l
    simp only [MulAction.compHom_smul_def] at H
    have H' : act g • c (h, l) - c (g * h, l) + c (g, h * l) - c (g, h) = 0 := by
      have h1 : act g • c (h, l) - c (g * h, l) + c (g, h * l) - c (g, h)
          = (act g • c (h, l) + c (g, h * l)) - (c (g * h, l) + c (g, h)) := by abel
      rw [h1, H]
      abel
    exact H'

end Work.SSGRoute
