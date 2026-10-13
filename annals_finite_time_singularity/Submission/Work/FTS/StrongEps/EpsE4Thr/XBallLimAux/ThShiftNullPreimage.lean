/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimAux/ThShiftNullPreimage.lean`

**The preimage of a null set under the angular shift is null.**

`thShift θ p = arctan (tan θ · e^{-p})` maps `Iθ = [0,π/2]` into itself (`thShift_mem`), and for
every fixed `p` the map `θ ↦ thShift θ p` is a smooth bijection of `(0,π/2)` (with inverse
`θ ↦ arctan (tan θ · e^{p})`); hence the preimage of a null set is null.  Rather than invoking
that smoothness, the proof uses the *substitution bound* `JepsHkMem.lintegral_thShift_le` in its
product form `FstarJepsSmoothAux.LintegralProdThShiftLe`: applied to the indicator of `Z` it
gives

  `∫⁻_{(θ,p) ∈ Iθ × [-ε,ε]} 1_{thShift θ p ∈ Z} ≤ C · ∫⁻_{θ ∈ Iθ} 1_{θ ∈ Z} = C · μ_{Iθ}(Z) = 0`,

so the indicator vanishes a.e., which is exactly the vanishing of the product measure of the
preimage.

This file is the *clean* replacement of `FstarJepsSmoothAux.ThShiftPreimageNull` (which carries a
`sorry`); it is consumed by `XBallLimAux.MajorantIntegrable`, the cloned copy of the majorant
integrability lemma, so that `XBallLimAux.FstarPzJepsSmooth` — the `fsm` input of the class-`C`
clause at the *limit* slice of the local step — has a `sorry`-free dependency cone.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftAEMeasurable
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.LintegralProdThShiftLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

set_option autoImplicit false

/-- **The angular shift pulls back product-null sets to null sets.**  For `ε > 0` and a null
measurable set `Z ⊆ ℝ`, the set of `(θ,p) ∈ Iθ × [-ε,ε]` with `thShift θ p ∈ Z` has vanishing
product measure. -/
theorem thShift_null_preimage {ε : ℝ} (hε : 0 < ε) {Z : Set ℝ} (hZ : MeasurableSet Z)
    (hZ0 : (MeasureTheory.volume : MeasureTheory.Measure ℝ) Z = 0) :
    ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))
      {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z} = 0 := by
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) with hμ
  -- the indicator of `Z`, as a measurable `ℝ≥0∞`-valued function
  have hU : Measurable (Z.indicator (fun _ : ℝ => (1 : ENNReal))) :=
    measurable_const.indicator hZ
  -- its angular lintegral vanishes
  have hZ01 : (∫⁻ θ in Work.Spaces.Iθ, Z.indicator (fun _ : ℝ => (1 : ENNReal)) θ) = 0 := by
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, Z.indicator (fun _ : ℝ => (1 : ENNReal)) θ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iθ) Z := by
      rw [MeasureTheory.lintegral_indicator hZ, MeasureTheory.setLIntegral_const, one_mul]
    rw [h1, MeasureTheory.Measure.restrict_apply hZ]
    exact measure_mono_null Set.inter_subset_left hZ0
  -- the shift bound, applied to the indicator
  have hAEM : AEMeasurable
      (fun x : ℝ × ℝ => Z.indicator (fun _ : ℝ => (1 : ENNReal))
        (Work.FTS.StrongEps.thShift x.1 x.2)) μ :=
    hU.aemeasurable.comp_aemeasurable
      (Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.aemeasurable_thShift_prod (ε := ε))
  have hInt0 : (∫⁻ x, Z.indicator (fun _ : ℝ => (1 : ENNReal))
      (Work.FTS.StrongEps.thShift x.1 x.2) ∂μ) = 0 := by
    have h := Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.LintegralProdThShiftLe
      (ε := ε) hε hU
    rw [hZ01, mul_zero] at h
    exact le_antisymm h bot_le
  -- hence the indicator vanishes a.e.
  have hae : (fun x : ℝ × ℝ => Z.indicator (fun _ : ℝ => (1 : ENNReal))
      (Work.FTS.StrongEps.thShift x.1 x.2)) =ᵐ[μ] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff' hAEM).mp hInt0
  -- rewrite the preimage as the set where the indicator does not vanish
  have hset : {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z}
      = {x : ℝ × ℝ | Z.indicator (fun _ : ℝ => (1 : ENNReal))
          (Work.FTS.StrongEps.thShift x.1 x.2) ≠ 0} := by
    ext x
    by_cases hx : Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z <;> simp [hx]
  rw [hset]
  exact ae_iff.mp hae

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
