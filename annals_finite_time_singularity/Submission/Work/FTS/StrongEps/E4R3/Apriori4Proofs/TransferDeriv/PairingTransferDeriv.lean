import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Transfer
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.KernelFacts
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat
import Submission.Work.FTS.CoercivityStep.Base.H1IP_congr_qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PairingTransferDeriv` — the derivative-priced transfer estimate at the level of the pairing

`pairing_transfer_deriv` is the log-coordinate transfer estimate for a weight `w` whose log
pull-back is log-Lipschitz, with the derivative price on the second argument: the analytic
content (the convolution on the log plane) is the hypothesis `PlaneTransferDeriv`, and the work
here is the two log-coordinate substitutions which turn the quadrant pairings into their plane
counterparts.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The derivative-priced transfer estimate in the quadrant form.** -/
theorem pairing_transfer_deriv {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hLT : PlaneTransferDeriv)
    {w : ℝ → ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hwsh : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwsh' : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p))
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    {g₁ g₂ : Fn} (hs1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g₁)
        Work.FTS.EllipticEst.Q0)
    (hs2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g₂) Work.FTS.EllipticEst.Q0)
    (hC2 : ContDiff ℝ 1 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂))
    (hJ1 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
        * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hJ2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
        * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hX1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
        => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y))
    (hX2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
        => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p))))
    (hG1 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * g₁ z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hG2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * g₂ z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2))
    (hF2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) y‖ ^ 2)) :
    |(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
        * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      - (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
          * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
          * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2)
            + Real.sqrt (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
                * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) y‖ ^ 2)) := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hc1 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs1
  have hc2 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs2
  have hkabs : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) ≤ 1 := by
    have h1 : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) = 1 := by
      rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p|) = Work.FTS.StrongEps.Jker ρ ε
        from funext (fun p => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε p))]
      exact Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0
    rw [h1]
  have hT := hLT hε0 hε1 hCw (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).measurable
    (Work.FTS.StrongEps.Jker_integrable hρ.moll hε0) hkabs
    (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
    hw0 hwm hwsh hwsh' hc1.measurable hc2.measurable hC2
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc1 y)
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc2 y)
    hI1 hI2 hF2
  have hm1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
        * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ1]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y)
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ) :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) hX1
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    show Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * (w (Real.exp s) (Real.arctan (Real.exp ζ))
            * Work.FTS.StrongEps.Jeps ρ ε g₁ (Real.exp s) (Real.arctan (Real.exp ζ))
            * g₂ (Real.exp s) (Real.arctan (Real.exp ζ)))
      = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p)))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ)
    have hJ : Work.FTS.StrongEps.Jeps ρ ε g₁ (Real.exp s) (Real.arctan (Real.exp ζ))
        = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p) :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε g₁ (s, ζ)
    rw [hJ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply]
    ring
  have hm2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
        * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p)) := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ2]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p)))
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p)) :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p))) hX2
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    show Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * (w (Real.exp s) (Real.arctan (Real.exp ζ))
            * g₁ (Real.exp s) (Real.arctan (Real.exp ζ))
            * Work.FTS.StrongEps.Jeps ρ ε g₂ (Real.exp s) (Real.arctan (Real.exp ζ)))
      = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ))
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p))
    have hJ : Work.FTS.StrongEps.Jeps ρ ε g₂ (Real.exp s) (Real.arctan (Real.exp ζ))
        = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p) :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε g₂ (s, ζ)
    rw [hJ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply]
    ring
  have hq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG1]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2)
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)) ^ 2 :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2) hI1
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  have hq2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG2]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2)
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ)) ^ 2 :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2) hI2
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  rw [hm1, hm2, hq1, hq2]
  exact hT

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
