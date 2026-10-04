import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.ODE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

theorem isSymm_addSec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h) :
    Work.Diff.STE.D.IsSymm (I := I) (Work.Diff.STE.D.addSec (I := I) g₀ h) := by
  -- `IsSymm` is pointwise symmetry of the bilinear form; `addSec` adds the (symmetric) inner
  -- product of `g₀` to the (symmetric) section `h`.
  intro x u v
  simp only [addSec_apply, hsym x u v, g₀.symm x u v]

end Work.Diff.STE.D
