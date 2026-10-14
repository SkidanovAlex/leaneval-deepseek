import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EpsEngine.mixed_logCoords
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
-- ===== merged: Submission.Work.FTS.EpsEngine.mixed_Jeps_kernel_locInt =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_E_of_EllLimOK3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem contDiffOn_two_E_of_EllLimOK3 {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E)
    {fn : ℕ → Fn} {f : Fn} {B : ℝ}
    (hC : ∀ n, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd)
    (hj : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) :
    ContDiffOn ℝ 2 (Function.uncurry (E f)) Work.FTS.EllipticEst.Q0 := by
  have h3 := (h fn f B hC hB h4 hj).2.1
  have hQ : Work.FTS.EllipticEst.Q0 = Work.Construction.Qd := rfl
  rw [hQ]
  exact h3.of_le (by norm_num)

end Work.FTS.StrongEps
end
end
