import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.PhiProps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- The bilinear coherent-state expansion of `⟪Φ Ψ z, B (Φ Ψ' z)⟫` for an
arbitrary (not necessarily continuous) spectator operator `B`: the finite double
sum over the condensate levels of `Ψ` and `Ψ'`, weighted by
`conj(cohWeight n z) * cohWeight m z`.  This is the `B`-twisted companion of the
expansion of `⟪Φ Ψ z, Φ Ψ' z⟫` used in the Bargmann isometry. -/
theorem inner_Phi_PhiB_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : E →ₗ[ℂ] E) (Ψ Ψ' : Work.BoseB4.FockCore E) (z : ℂ) :
    inner ℂ (Work.BoseB4.Phi Ψ z) (B (Work.BoseB4.Phi Ψ' z))
      = ∑ n ∈ Ψ.support, ∑ m ∈ Ψ'.support,
          ((starRingEnd ℂ (Work.BoseB4.cohWeight n z)) * Work.BoseB4.cohWeight m z)
            * inner ℂ (Ψ n) (B (Ψ' m)) := by
  rw [Phi_apply, Phi_apply]
  simp only [map_sum, map_smul]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

end Work.BoseB4
