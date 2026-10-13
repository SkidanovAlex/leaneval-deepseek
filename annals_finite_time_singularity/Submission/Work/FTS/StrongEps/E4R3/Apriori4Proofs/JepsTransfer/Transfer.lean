import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.KernelFacts
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.continuous_logW_leaf
import Submission.Work.FTS.CoercivityStep.Base.H1IP_congr_qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Transfer.lean` — the weighted transfer estimate for the mollifier

This is the assembly of the log-coordinate transfer estimate: for a weight `w` whose log
pull-back `logW w` is nonnegative, measurable and log-Lipschitz in both directions, and two
profiles `g₁`, `g₂` smooth on the open quadrant,

  `|∫_Quad w · (J_ε g₁) · g₂ − ∫_Quad w · g₁ · (J_ε g₂)| ≤ C ε √(∫_Quad w g₁²) √(∫_Quad w g₂²)`

— with **no derivative loss**.  The analytic content (the even convolution on the log plane)
is isolated in the hypothesis `LogPlaneTransfer`; the work here is the two log-coordinate
substitutions (`integral_quad_log_subst`), which turn each of the four quadrant integrals into
its plane counterpart, and the identification `logPull (J_ε g) = ∫_p Jker ρ ε p · logPull g (·−p)`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The log-plane transfer inequality**, abstracted: this is exactly the conclusion of
`JepsTransfer.logPair_conv_transfer_iter` with its hypotheses bound. -/
def LogPlaneTransfer : Prop :=
  ∀ {k : ℝ × ℝ → ℝ} {ε Cw : ℝ}, 0 < ε → ε ≤ 1 → 0 ≤ Cw →
    Continuous k → (∀ p : ℝ × ℝ, 0 ≤ k p) → (∫ p : ℝ × ℝ, k p = 1) →
    (∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) →
    (∀ p : ℝ × ℝ, k (-p) = k p) →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * (|p.1| + |p.2|)) →
    ∀ {Q : ℝ × ℝ → ℝ}, (∀ y : ℝ × ℝ, 0 ≤ Q y) → Measurable Q →
    (∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y) →
    (∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p)) →
    ∀ {G₁ G₂ : ℝ × ℝ → ℝ}, Measurable G₁ → Measurable G₂ →
    (∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p))) →
    (∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p))) →
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2) →
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2) →
    |(∫ s, ∫ ζ, Q (s, ζ) * (∫ p : ℝ × ℝ, k p * G₁ ((s, ζ) - p)) * G₂ (s, ζ))
      - (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) * (∫ p : ℝ × ℝ, k p * G₂ ((s, ζ) - p)))|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) ^ 2)
          * Real.sqrt (∫ s, ∫ ζ, Q (s, ζ) * G₂ (s, ζ) ^ 2)

/-- The mollifier as a convolution, in the form matching `logPull`. -/
theorem logPull_Jeps_apply (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fn) (y : ℝ × ℝ) :
    Work.FTS.StrongEps.Jeps ρ ε g (Real.exp y.1) (Real.arctan (Real.exp y.2))
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y - p) := by
  rw [← Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_Jeps_eq ρ ε g y]
  rfl

/-- **The weighted transfer estimate in the quadrant form.** -/
theorem pairing_transfer {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (hLT : LogPlaneTransfer)
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
    (hJ1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hJ2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hG1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * g₁ z θ ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hG2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * g₂ z θ ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2)) :
    |(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      - (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2) := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hc1 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs1
  have hc2 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs2
  -- the abstract log-plane transfer
  have hT := hLT hε0 hε1 hCw (Work.FTS.StrongEps.Jker_continuous hρ.moll ε)
    (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε)
    (Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0)
    (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_even hρs ε)
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_momint hρ.moll hε0)
    hw0 hwm hwsh hwsh' hc1.measurable hc2.measurable
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc1 y)
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc2 y) hI1 hI2
  -- the four conversions
  have hm1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ) := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ1]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      logPull_Jeps_apply ρ ε g₁ (s, ζ)]
    ring
  have hm2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p)) := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ2]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      logPull_Jeps_apply ρ ε g₂ (s, ζ)]
    ring
  have hq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG1]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  have hq2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ)) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG2]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  rw [hm1, hm2, hq1, hq2]
  exact hT

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
