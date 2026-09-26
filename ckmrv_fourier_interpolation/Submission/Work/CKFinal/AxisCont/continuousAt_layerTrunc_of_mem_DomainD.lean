import Mathlib
import Submission.Work.CKFinal.AxisCont.Basic
import Submission.Work.CKFinal.AxisCont.trunc_integrand_dominated
import Submission.Work.CKFinal.AxisCont.trunc_integrand_ae_data
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.Kaxis_bounded_compact
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.cuspExpansionKernel
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.LayerCont.AexpLow
import Submission.Work.LayerCont.TailIntegrable

namespace Work.CKFinal.AxisCont

open MeasureTheory Filter Topology
open scoped Topology

theorem continuousAt_layerTrunc_of_mem_DomainD (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD) :
    ContinuousAt (fun τ : UpperHalfPlane =>
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) τ₁ := by
  obtain ⟨ρ, hρ, bound, hbint, hb⟩ := trunc_integrand_dominated ℓ d hd r hτ₁
  obtain ⟨hmeas, hcont⟩ := trunc_integrand_ae_data ℓ d hd r hτ₁
  have hmain : ContinuousAt (fun τ : UpperHalfPlane =>
      ∫ t, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ)))) τ₁ :=
    MeasureTheory.continuousAt_of_dominated (μ := MeasureTheory.volume.restrict (Set.Ici (1 : ℝ)))
      (F := fun τ t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (x₀ := τ₁) (bound := bound) hmeas ?_ hbint hcont
  · simpa only [Work.Asymptotics.layerTrunc] using hmain.const_mul (Work.Asymptotics.sinSq r)
  · filter_upwards [Metric.closedBall_mem_nhds τ₁ hρ] with τ hτ
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr ?_
    exact Filter.Eventually.of_forall fun t ht => hb τ t hτ ht

end Work.CKFinal.AxisCont
