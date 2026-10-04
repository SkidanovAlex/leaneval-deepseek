import Mathlib
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

theorem formInFrame_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} {A : Work.Diff.EXT.MatE (E := E)} (h : ∀ i j, A i j = A j i) :
    ∀ u v : TangentSpace I x,
      Work.Diff.EXT.formInFrame (I := I) x₀ x A u v
        = Work.Diff.EXT.formInFrame (I := I) x₀ x A v u := by
  intro u v
  rw [formInFrame_apply, formInFrame_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h i j]
  ring

end Work.Diff.EXT
