import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.LieMet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

theorem isSymm_deTurckSec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (hLC : Submission.Diff.LCSmooth I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.D.IsSymm (I := I)
      (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsmooth) := by
  -- `IsSymm` unfolds to pointwise symmetry of the bilinear form.
  intro x u v
  -- Unfold the definition of `deTurckSec` (through its packaging `deTurckCLM`) and of the DeTurck
  -- operator `P(g) = -2 Ric(g) + L_{W(g)} g`.
  rw [Work.Diff.STE.D.deTurckSec_apply hLC g₀ h hsym hpos hsmooth x u v,
      Work.Diff.STE.D.deTurckSec_apply hLC g₀ h hsym hpos hsmooth x v u,
      Work.Diff.STE.DeTurck.deTurckOp_apply, Work.Diff.STE.DeTurck.deTurckOp_apply]
  -- Smoothness of the Levi-Civita connection of the metric `g = smetOf h …`.
  have hcov := (hLC (Work.Diff.STE.D.smetOf h hsym hpos hsmooth)).1.some
  -- The Ricci tensor of the Levi-Civita connection is symmetric, and the Lie derivative of the
  -- metric is symmetric because the metric is.
  rw [Work.Diff.EXT.ricAt_symm_L hLC (Work.Diff.STE.D.smetOf h hsym hpos hsmooth) hcov x u v,
      Work.Diff.STE.DeTurck.lieMet_comm (Work.Diff.STE.D.smetOf h hsym hpos hsmooth) _ x u v]

end Work.Diff.STE.D
