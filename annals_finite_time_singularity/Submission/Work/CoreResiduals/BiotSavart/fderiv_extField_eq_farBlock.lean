import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.radGreen_general_bound
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta
import Submission.Work.R1G.vecResid_eq_scalar_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The Fréchet derivative of the extended space-time Biot–Savart field is the far-block operator
on the strip.**

`extField ω S` is the space-time field of the two-sided time extension `windowExt ω S`
(`fun p => BS (windowExt ω S · p.2) p.1`), which agrees with `fun p => BS (ω · p.2) p.1` on the
strip `univ ×ˢ Icc 0 S`; `farBlock ω p` is the operator whose spatial block is the
Calderón–Zygmund derivative `fderiv ℝ (BS (ω·p.2)) p.1` and whose time block is `BS (∂ₜω(·,p.2)) p.1`.

For `0 < α`, `0 < S` and a strip-bundle vorticity `ω`, the two coincide at every point of the strip.

**Proof.** `windowExt_windowBundle` (with the `x`-Hölder regularity of `∂ₜω` from
`timeDeriv_xHolderOn_general`) gives the window bundle of the extension, so
`biotSavartSpacetimeC1_of_dtContinuous` gives `ContDiffAt ℝ 1 (extField ω S) p` at every `p` of the
strip; hence `extField ω S` is differentiable there with derivative `fderiv ℝ (extField ω S) p`. The
two blocks of that derivative are identified on the strip by `fderiv_slice_ext_eq` (spatial block:
`fderiv ℝ (BS (ω·t)) x`) and `fderiv_time_ext_eq` (time block at `1`:
`BS (∂ₜ(windowExt ω S)(·,t)) x = BS (∂ₜω(·,t)) x`, the last equality by `dtExt_of_mem_Icc`). A
continuous linear map `ℝ³ × ℝ →L[ℝ] ℝ³` is determined by its values on `inl v` and `inr 1` (every
`q` is `inl q.1 + inr q.2`), and `farBlock_apply` gives the same decomposition for `farBlock ω p`. -/
theorem fderiv_extField_eq_farBlock {α : NNReal} (hα : 0 < (α : ℝ))
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∀ p ∈ Set.univ ×ˢ Set.Icc (0:ℝ) S,
      fderiv ℝ (Work.CoreResiduals.BiotSavart.extField ω S) p
        = Work.CoreResiduals.BiotSavart.farBlock ω p := by
  intro p hp
  obtain ⟨x, t⟩ := p
  have ht : t ∈ Set.Icc (0:ℝ) S := hp.2
  have hdiff := hbun.2.1.1
  have hRpos : 0 < R := hbun.1.1
  -- the extension satisfies the window bundle and has continuous `∂ₜ`-slices
  obtain ⟨hadmw, hdtc⟩ :=
    windowExt_windowBundle hα hS hbun (timeDeriv_xHolderOn_general hα hS hbun)
  have hpre : t ∈ Work.ConstructionInstance.preWindow (S + 1) := by
    change t ∈ Set.Ioo (-2 : ℝ) (S + 1)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the extension is `C¹` at every point of the strip
  have hcd : ContDiffAt ℝ 1 (Work.CoreResiduals.BiotSavart.extField ω S) (x, t) :=
    biotSavartSpacetimeC1_of_dtContinuous hadmw hdtc x t hpre
  -- the two blocks of the derivative
  have hblock1 : ∀ v : R3,
      (fderiv ℝ (Work.CoreResiduals.BiotSavart.extField ω S) (x, t))
          (ContinuousLinearMap.inl ℝ R3 ℝ v)
        = fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x v := by
    intro v
    rw [fderiv_slice_ext_eq (x := x) (t := t) ht hcd]
    rfl
  have hblock2 : (fderiv ℝ (Work.CoreResiduals.BiotSavart.extField ω S) (x, t))
        (ContinuousLinearMap.inr ℝ R3 ℝ 1)
      = Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x := by
    have hagree : (fun y : R3 => FiniteTimeSingularity.timeDeriv ω y t)
        = (fun y : R3 =>
            FiniteTimeSingularity.timeDeriv (Work.CoreResiduals.BiotSavart.windowExt ω S) y t) := by
      funext y
      rw [timeDeriv_windowExt hS hdiff y t, dtExt_of_mem_Icc ht]
    rw [hagree]
    exact (fderiv_time_ext_eq (x := x) (t := t) hRpos hadmw ht hcd).symm
  -- a continuous linear map out of a product is determined by its two blocks
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨v, s⟩ := w
  rw [farBlock_apply]
  have hsplit : (v, s) = ContinuousLinearMap.inl ℝ R3 ℝ v
      + ContinuousLinearMap.inr ℝ R3 ℝ s := by
    ext <;> simp
  rw [hsplit, map_add, hblock1 v]
  have hsmul : (fderiv ℝ (Work.CoreResiduals.BiotSavart.extField ω S) (x, t))
        (ContinuousLinearMap.inr ℝ R3 ℝ s)
      = s • (fderiv ℝ (Work.CoreResiduals.BiotSavart.extField ω S) (x, t))
        (ContinuousLinearMap.inr ℝ R3 ℝ 1) := by
    rw [show ContinuousLinearMap.inr ℝ R3 ℝ s
        = s • ContinuousLinearMap.inr ℝ R3 ℝ 1 from by ext <;> simp]
    rw [map_smul]
  rw [hsmul, hblock2]

end Work.CoreResiduals.BiotSavart
