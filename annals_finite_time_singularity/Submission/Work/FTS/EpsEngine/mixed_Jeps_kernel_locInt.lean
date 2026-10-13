/-
# `mixed_Jeps_kernel_locInt`: the all-routed kernel representation of `D_z^j D_θ^i (J_ε f)`
for a **merely locally integrable** profile

`J_ε = Jeps ρ ε` is the log-coordinate mollifier of `Work.FTS.StrongEps`; in the log coordinates
`s = log z`, `ζ = log tan θ` it is the convolution of `Jker ρ ε` with `logPull f`
(`Work.FTS.StrongEps.Jeps_eq_conv`), so `D_z = ∂_s` and `D_θ = 2 ∂_ζ` act on the **kernel**.

This module proves the resulting identity: for `f` whose log-pull is only *locally integrable*
(no smoothness at all),

`D_z^j D_θ^i (J_ε f) z θ = 2^i ∫ p, ∂₁^j ∂₂^i (Jker ρ ε) p · f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))`.

This is the whole point of the log coordinates: every derivative can be moved onto the smooth,
compactly supported kernel, so the estimate only ever needs the *weighted* norms of `f` (never its
derivatives at the boundaries of the quadrant).  The same statement *with* the hypothesis that `f`
is `C^∞` on the quadrant is `Work.FTS.StrongEps.mixed_Jeps_kernel_partial`
(`j' = i' = 0`), whose proof routes through the commutation `mixed_Jeps` and an integration by
parts in `p`; that proof cannot be reused here, because `f` has no derivatives.

## The proof

* `Work.FTS.EpsEngine.conv_Kd` (`Submission/Work/FTS/EpsEngine/ConvDeriv.lean`): the derivative
  `∂₁^j ∂₂^i` of a convolution with a `C^∞`, compactly supported kernel is the convolution with
  `Kd A j i = ∂₁^j∂₂^i A`.  This holds for a merely locally integrable second factor, the
  derivative being pushed onto the kernel by a change of variable in `p`
  (`HasCompactSupport.hasFDerivAt_convolution_left`).
* `Work.FTS.EpsEngine.mixed_logCoords` (`Submission/Work/FTS/EpsEngine/mixed_logCoords.lean`):
  the chain rule `D_z = ∂_s`, `D_θ = 2 ∂_ζ` under `(z,θ) ↦ (log z, log tan θ)`.
* `Jeps_eq_conv` identifies `J_ε f` with that convolution on the open quadrant, and
  `logPull_shift` is the identity `logPull f (s - p₁, ζ - p₂) = f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.EpsEngine.ConvDeriv
import Submission.Work.FTS.EpsEngine.mixed_logCoords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.StrongEps

theorem mixed_Jeps_kernel_locInt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : Work.FTS.Galerkin.Fn}
    (hf : MeasureTheory.LocallyIntegrable (Work.FTS.StrongEps.logPull f) MeasureTheory.volume)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = (2 : ℝ) ^ i * ∫ p : ℝ × ℝ,
          Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) j i p
          * f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
  -- the convolution in the log coordinates
  set Ψ : ℝ × ℝ → ℝ := fun X => ∫ p : ℝ × ℝ, Jker ρ ε p * logPull f (X - p) with hΨ
  -- it is `C^∞`, being the convolution of a `C^∞` compactly supported kernel with a locally
  -- integrable function
  have hΨsm : ∀ n : ℕ, ContDiff ℝ n Ψ := by
    intro n
    have h := (hasCompactSupport_Jker ρ hρ hε).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_Jker ρ hρ ε n) hf
    rw [hΨ, ← contDiffOn_univ]
    refine ContDiffOn.congr
      (f := (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] logPull f))
      ?_ (fun X _ => ?_)
    · rwa [contDiffOn_univ]
    · rw [MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- `J_ε f` agrees with `Ψ (log z, log tan θ)` on the open quadrant
  have hEq : Set.EqOn (Function.uncurry (Jeps ρ ε f))
      (Function.uncurry (fun z θ => Ψ (sOf z, zetaOf θ))) Quad := by
    intro p hp
    show Jeps ρ ε f p.1 p.2 = Ψ (sOf p.1, zetaOf p.2)
    rw [Jeps_eq_conv ρ ε f hp.1 hp.2, hΨ, MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- hence the framed derivatives agree on the open quadrant
  have hmain : Work.Spaces.mixed j i (Jeps ρ ε f) z θ
      = Work.Spaces.mixed j i (fun z θ => Ψ (sOf z, zetaOf θ)) z θ := by
    have h1 := Work.FTS.TransportS.DthIter_congrOn isOpen_Quad hEq i
    have h2 := Work.FTS.TransportS.DzIter_congrOn isOpen_Quad h1 j
    exact h2 (show (z, θ) ∈ Quad from ⟨hz, hθ⟩)
  -- the chain rule in the log coordinates
  have hlog := mixed_logCoords hΨsm hz hθ j i
  -- and the convolution derivatives, routed onto the kernel
  have hstep : Kd Ψ j i (sOf z, zetaOf θ)
      = ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j i p * logPull f ((sOf z, zetaOf θ) - p) := by
    rw [Kd_eq]
    simp only [hΨ]
    exact conv_Kd (fun n => Jker_smooth hρ ε) (hasCompactSupport_Jker ρ hρ hε) hf j i
      (sOf z) (zetaOf θ)
  rw [hmain, hlog, hstep]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only
  rw [show (sOf z, zetaOf θ) - p = (sOf z - p.1, zetaOf θ - p.2) from
    Prod.mk_sub_mk _ _ _ _, logPull_shift f hz hθ]

end Work.FTS.EpsEngine
