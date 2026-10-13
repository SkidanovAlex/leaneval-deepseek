/-
# `RouteB.ellNode8tr_body` — R5: the body of the trace-strengthened elliptic node

`cbc/fts_ellnode_ruling.md` §4.3 (R5): the assembly of the node
`PhiStar.EllNode8tr_holds` from the four ingredients of Route B′,

* **R1** `Honesty.exists_cptQ_approx_th 10` — compactly supported `C^∞` approximants `G n` of `F`
  with vanishing angular moment, converging in `ℋ^10` (the `θ`-trace form of the CptApp chain);
* **R2** `RouteB.bslSolExists_psiSeries_of_node_hyp 10` — the witness `Ψ`, which is the mode
  series of `F` on the open quadrant, solves `bslOp α Ψ = F`, has vanishing moment, and is
  smooth there;
* **R3** `RouteB.psiSeries_L2_of_approx 10` — the mode series of the approximants converge to `Ψ`
  in `L²(Q0)`;
* **R4** `RouteB.hkMem_slots_of_approx_pp 8` — the honesty of the three second-order slots
  `z²∂_z²Ψ`, `∂_θ²Ψ`, `z ∂_z ∂_θ²Ψ` at level `8`, which is the only part of `EllWeakPos α 8 F Ψ`
  not supplied directly by R2.

The statement is *frozen*: it is the expanded form of `PhiStar.EllNode8tr`, so that this module
does not have to import the (lead-installed) file that in turn imports it.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.PhiStar.ThetaTraces
import Submission.Work.FTS.PhiStar.Honesty.exists_cptQ_approx
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_psiSeries_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.PhiStar.RouteB.bslSolExists_psiSeries_of_node_hyp
import Submission.Work.FTS.PhiStar.RouteB.psiSeries_L2_of_approx
import Submission.Work.FTS.PhiStar.RouteB.hkMem_slots_of_approx_pp
import Submission.Work.FTS.StrongPersist.Basic

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
