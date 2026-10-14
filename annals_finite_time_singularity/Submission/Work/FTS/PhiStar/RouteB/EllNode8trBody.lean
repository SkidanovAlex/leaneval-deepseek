import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.PhiStar.RouteB.bslSolExists_psiSeries_of_node_hyp
import Submission.Work.FTS.PhiStar.RouteB.hkMem_slots_of_approx_pp
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Congr
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RouteB

/-- **R5, expanded form.**  See the module docstring. -/
theorem ellNode8tr_body :
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 10 F →
      Work.FTS.PhiStar.ThetaTraces α 10 F →
      (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (𝓝 0)) →
      ∃ Ψ : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.TT.EllWeakPos α 8 F Ψ ∧ Work.Elliptic.IsBslSol α F Ψ := by
  intro α F hα hα4 hsmF hF10 htr hFs hdec
  have hα1 : α ≤ 1 := by linarith
  -- ## R1: the compactly supported approximants
  obtain ⟨G, hGs, hGmem, hGconv⟩ :=
    Work.FTS.PhiStar.Honesty.exists_cptQ_approx_th 10 hα hα4 hsmF hF10 htr hFs
  -- ## R2: the witness
  obtain ⟨Ψ, hΨsm, hΨsol, hΨfstar, hΨseries⟩ :=
    bslSolExists_psiSeries_of_node_hyp 10 α F hα hα4 hsmF hF10 hFs hdec
  -- ## R3: the `L²(Q0)`-convergence of the approximating mode series to `Ψ`
  have hL2 := psiSeries_L2_of_approx 10 (by norm_num) hα hα4 hsmF hF10 G
    (fun n => (hGs n).1) (fun n => (hGs n).2) hGconv
    (fun z hz θ hθ hθ2 => hΨseries z hz θ hθ hθ2)
  -- ## R4: the three second-order slots of `Ψ` at level `8`
  obtain ⟨hslotA, hslotB, hslotC⟩ :=
    hkMem_slots_of_approx_pp 8 (by norm_num) hα hα4 hsmF hF10 G
      (fun n => (hGs n).1.smoothOpen)
      (fun n => Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem (hGs n).1 10)
      (fun n =>
        (Work.FTS.PhiStar.Honesty.ellWeakPos_psiSeries_of_cptQ 10 hα hα4
          (hGs n).1 (hGs n).2).1)
      hGconv hΨsm (fun z hz θ hθ hθ2 => hΨsol.1 z hz θ hθ hθ2) hL2.1 hL2.2
  -- ## the ten conjuncts of `EllWeakPos α 8 F Ψ`
  refine ⟨Ψ, ⟨hΨsol.1, hΨsol.2.1, hΨsol.2.2.1, hFs, hΨfstar,
    fun n => Work.FTS.EllipticEst.SmoothOpen.forall hΨsm n,
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsmF hF10,
    hslotA, hslotB, hslotC⟩, hΨsol⟩

end Work.FTS.PhiStar.RouteB
