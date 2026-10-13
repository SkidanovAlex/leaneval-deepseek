import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB4

open MeasureTheory Set Filter
open scoped Real Topology

/-- The pointwise bound on the low-order jets of the slices of `g`, in the exact shape of
`Work.FTS_RegExport.RXT.Slots.JetBnd`: for every fake time `τ ≥ 0`,
`|D_z^b D_θ^a (slice g τ)(z,θ)| ≤ C · z^{3/2}/(1+z)²` on the open quadrant, whenever
`a + b ≤ 2`.

This is the `LimApprox`-clause of `DynOK'` fed through the weighted limit transfer
`RXA2w.lim_mixed_weighted_proved`; the constant depends on the horizon `τ + 1` only, which is
harmless because the target statement is a pointwise differentiability statement. -/
theorem slice_jetBnd {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, 0 ≤ C ∧ Work.FTS_RegExport.RXT.Slots.JetBnd C (Work.FTS.Galerkin.slice g τ) := by
  have hα : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hα1 : Work.FTS.Regularity.pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  obtain ⟨C, hC0, hCb⟩ :=
    Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved hα hα1 hOK.2 (τ + 1) (by linarith)
  exact ⟨C, hC0, fun b a hab z θ hz h0 h1 =>
    hCb τ ⟨hτ, by linarith⟩ b a hab z θ hz h0 h1⟩

/-- The angular density `s ↦ L₁₂dens (slice g τ) s` of a slice of `g` is continuous on `(0,∞)`.

It is `Qang (slice g τ) 0 s / s` (`Elliptic.L12dens_eq_Qang_div`), and `Qang (slice g τ) 0` is
differentiable on `(0,∞)` with derivative `Qang (slice g τ) 1 s / s`
(`RXT.Slots.QangZeroDeriv_jet`, differentiation under the angular integral). -/
theorem slice_L12dens_continuousOn {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ContinuousOn (fun s => Work.Elliptic.L12dens (Work.FTS.Galerkin.slice g τ) s) (Ioi 0) := by
  obtain ⟨C, hC0, hJet⟩ := slice_jetBnd ha ha13 hOK τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  refine ContinuousOn.congr (s := Ioi 0)
    (f := fun s => Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 s / s)
    (g := fun s => Work.Elliptic.L12dens (Work.FTS.Galerkin.slice g τ) s) ?_ ?_
  · intro s hs
    exact ((Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0 h4 hJet hs).continuousAt.div
      continuousAt_id (ne_of_gt hs)).continuousWithinAt
  · intro s _
    exact Work.Elliptic.L12dens_eq_Qang_div (Work.FTS.Galerkin.slice g τ) s

theorem slice_L12_c2 {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) w)
        (-(Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) z)) z ∧
      DifferentiableAt ℝ (fun w => Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) w) z := by
  intro τ hτ z hz
  obtain ⟨C, hC0, hJet⟩ := slice_jetBnd ha ha13 hOK τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  have hcont := slice_L12dens_continuousOn ha ha13 hOK τ hτ
  -- the fundamental theorem of calculus for the tail integral `z ↦ ∫_z^∞ L₁₂dens`
  have hint : IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) s)
      (Ioi (z / 2)) :=
    hJet.dens_integrable hC0 hcont (by linarith)
  have hderiv : HasDerivAt
      (fun σ => Work.FM.L12 Work.Spaces.K (Work.FTS.Galerkin.slice g τ) σ)
      (-(Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) z)) z :=
    Work.FM.hasDerivAt_L12_of_integrable (K := Work.Spaces.K)
      (f := Work.FTS.Galerkin.slice g τ) (a := z / 2) (ρ := z) hint
      (fun s _ => hcont.continuousAt (isOpen_Ioi.mem_nhds (show (0 : ℝ) < s by linarith)))
      (by linarith)
  refine ⟨?_, ?_⟩
  · -- `L₁₂` is the fundamental-model operator with `K = 3 sin θ cos²θ`
    simpa only [Work.Construction.L12, Work.Construction.L12dens] using hderiv
  · -- the density is `Qang · 0 / s`, and `Qang · 0` is differentiable on `(0,∞)`
    have hd : DifferentiableAt ℝ
        (fun w => Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 w / w) z :=
      (Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0 h4 hJet hz).differentiableAt.div
        differentiableAt_id (ne_of_gt hz)
    have hcongr : (fun w => Work.Elliptic.L12dens (Work.FTS.Galerkin.slice g τ) w)
        =ᶠ[𝓝 z] (fun w => Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 w / w) :=
      Eventually.of_forall fun w =>
        Work.Elliptic.L12dens_eq_Qang_div (Work.FTS.Galerkin.slice g τ) w
    have h'' : DifferentiableAt ℝ
        (fun w => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) w) z :=
      hd.congr_of_eventuallyEq hcongr
    exact h''

end Work.FTS_StreamBdry.SB4
