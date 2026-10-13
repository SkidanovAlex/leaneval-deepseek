import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ContinuousMap.Algebra
import Submission.Work.FTS.GalBasis.PolySumDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

open scoped BigOperators

theorem isPolySum_add {s : Set (ℝ × ℝ)} {g₁ g₂ : C(s, ℝ)}
    (h₁ : Work.FTS.GalBasis.IsPolySum g₁) (h₂ : Work.FTS.GalBasis.IsPolySum g₂) :
    Work.FTS.GalBasis.IsPolySum (g₁ + g₂) := by
  obtain ⟨ι₁, _, a₁, b₁, c₁, hc₁⟩ := h₁
  obtain ⟨ι₂, _, a₂, b₂, c₂, hc₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim a₁ a₂, Sum.elim b₁ b₂, Sum.elim c₁ c₂, ?_⟩
  intro x
  rw [ContinuousMap.add_apply, hc₁ x, hc₂ x, Fintype.sum_sum_type]
  congr 1

end Work.FTS.GalBasis
