import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.TransferAux
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JepsQuadSq
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.PairingTransferDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logW_fderiv_integral_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.BaseCase
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_pairing_Jeps
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem slot_transfer_deriv {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hLT : PlaneTransferDeriv) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ {w : ℝ → ℝ → ℝ} {a b : ℕ}, Work.FTS.TransportS.IsLeafW α a w → a + b ≤ 4 →
      ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
      SlotIntegrableDeriv ρ ε w a b u v →
      |Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
          (Work.Spaces.mixed b a v)
        - Work.Coercivity.wip w (Work.Spaces.mixed b a u)
            (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))|
        ≤ C * ε * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a u)
              (Work.Spaces.mixed b a u))
          * (Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a v)
                (Work.Spaces.mixed b a v))
            + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a v)
                (Work.Spaces.mixed (b + 1) a v))
            + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) v)
                (Work.Spaces.mixed b (a + 1) v))) := by
  obtain ⟨Cl, hCl0, hCl⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform
  refine ⟨200 * (Cl + 1) * Real.exp (4 * Cl), by positivity, ?_⟩
  intro α hα ε hε w a b hleaf hab u v hu hv hInt
  have hε0 : 0 < ε := hε.1
  have hw' : w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
      ∨ w = Work.FTS.TransportS.leafGam α := by
    rcases hleaf with h | h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hsh := hCl α hα w hw'
  have hwsh : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
      ≤ Real.exp (Cl * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y :=
    fun y p => (hsh y p).1
  have hwsh' : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      ≤ Real.exp (Cl * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p) :=
    fun y p => (hsh y p).2
  have hw0 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logW_nonneg_of_leaf hleaf
  have hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.continuous_logW_leaf hw').measurable
  have hg1sm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed b a u))
      Work.FTS.EllipticEst.Q0 := fun n => (hu.mixed b a).forall n
  have hg2sm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed b a v))
      Work.FTS.EllipticEst.Q0 := fun n => (hv.mixed b a).forall n
  have hC2 : ContDiff ℝ 1 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull
      (Work.Spaces.mixed b a v)) := contDiff_one_logPull_of_forall hg2sm
  -- the diagonal integrability facts
  have hG1 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * Work.Spaces.mixed b a u z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := hInt.1.restrict
  have hG2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * Work.Spaces.mixed b a v z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := hInt.2.1.restrict
  have hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) y) ^ 2) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.integrable_logW_sq_of_lintegral hw0 hwm
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg1sm).aemeasurable
      (quad_lint_ne_top hInt.1)
  have hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) y) ^ 2) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.integrable_logW_sq_of_lintegral hw0 hwm
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg2sm).aemeasurable
      (quad_lint_ne_top hInt.2.1)
  -- the `θ`-slot integrability of `v` (the derivative price)
  have hDz2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * (Work.Spaces.Dz (Work.Spaces.mixed b a v) z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := hInt.2.2.2.2.1.restrict
  have hDth2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * (Work.Spaces.Dth (Work.Spaces.mixed b a v) z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
    have hraw : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed b (a + 1) v z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := hInt.2.2.2.2.2.restrict
    refine hraw.congr ?_
    refine (MeasureTheory.ae_restrict_mem
      (Work.FTS.StrongEps.isOpen_Quad.measurableSet)).mono (fun q hq => ?_)
    have hkey : Work.Spaces.Dth (Work.Spaces.mixed b a v) q.1 q.2
        = Work.Spaces.mixed b (a + 1) v q.1 q.2 :=
      Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
        (V := Work.FTS.StrongEps.Quad) Work.FTS.StrongEps.isOpen_Quad
        (g := Work.Spaces.DthIter a v) (fun n => (hv.DthIter a).forall n) b 1 hq
    show w q.1 q.2 * (Work.Spaces.mixed b (a + 1) v q.1 q.2) ^ 2
        = w q.1 q.2 * (Work.Spaces.Dth (Work.Spaces.mixed b a v) q.1 q.2) ^ 2
    rw [hkey]
  have hF2le := (logW_fderiv_integral_le hw0 hwm hg2sm hDz2 hDth2).2
  have hF2 := (logW_fderiv_integral_le hw0 hwm hg2sm hDz2 hDth2).1
  -- the `(a+1)`-slot of `v`, rewritten in the `D_θ` form
  have hDthcongr : Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) v)
        (Work.Spaces.mixed b (a + 1) v)
      = Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
          (Work.Spaces.Dth (Work.Spaces.mixed b a v)) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_both (ρ := w)
      (A := Work.Spaces.mixed b (a + 1) v) (A' := Work.Spaces.Dth (Work.Spaces.mixed b a v))
      (B := Work.Spaces.mixed b (a + 1) v) (B' := Work.Spaces.Dth (Work.Spaces.mixed b a v))
      (fun z θ h => (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
        (V := Work.FTS.StrongEps.Quad) Work.FTS.StrongEps.isOpen_Quad
        (g := Work.Spaces.DthIter a v) (fun n => (hv.DthIter a).forall n) b 1 h).symm)
      (fun z θ h => (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
        (V := Work.FTS.StrongEps.Quad) Work.FTS.StrongEps.isOpen_Quad
        (g := Work.Spaces.DthIter a v) (fun n => (hv.DthIter a).forall n) b 1 h).symm)
  -- the cross-term integrabilities
  have hJ2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * Work.Spaces.mixed b a u z θ
      * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v) z θ))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
    have hraw : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
        * Work.Spaces.mixed b a u z θ
        * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v) z θ))
        (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := hInt.2.2.2.1.restrict
    refine hraw.congr ?_
    refine (MeasureTheory.ae_restrict_mem
      (Work.FTS.StrongEps.isOpen_Quad.measurableSet)).mono (fun q hq => ?_)
    show w q.1 q.2 * Work.Spaces.mixed b a u q.1 q.2
          * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v) q.1 q.2
        = w q.1 q.2 * Work.Spaces.mixed b a u q.1 q.2
          * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v) q.1 q.2
    rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε0 (fun n => hv.forall n) hq.1 hq.2 b a]
  have hJ1 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ * Work.Spaces.mixed b a v z θ))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
    have hside : MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2
        * (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) q.1 q.2) ^ 2)
        (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) :=
      jeps_quad_sq_integrable hρ hCl0 hε0 hleaf hw0 hwm hwsh' hg1sm hI1
    refine integrable_cross_of_diag (μ := MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad)
      (w := w) (A := fun z θ => Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ)
      (B := fun z θ => Work.Spaces.mixed b a v z θ) ?_ ?_ hside ?_
    · refine (MeasureTheory.ae_restrict_mem
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet)).mono (fun q hq => ?_)
      exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf q.1 ⟨hq.2.1.le, hq.2.2.le⟩
    · exact (((Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW
          hleaf).mul
        (Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hg1sm 0).continuousOn).mul
          ((hv.mixed b a).forall 0).continuousOn).aestronglyMeasurable
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet)
    · exact hG2
  -- the plane integrability of the two cross terms
  have hconvm1 : AEStronglyMeasurable (fun y : ℝ × ℝ => ∫ p : ℝ × ℝ,
      Work.FTS.StrongEps.Jker ρ ε p
        * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) (y - p))
      MeasureTheory.volume :=
    ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous
        (fun n => Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hg1sm n)).aestronglyMeasurable).congr
      (Eventually.of_forall (fun y =>
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε
          (Work.Spaces.mixed b a u) y)))
  have hconvm2 : AEStronglyMeasurable (fun y : ℝ × ℝ => ∫ p : ℝ × ℝ,
      Work.FTS.StrongEps.Jker ρ ε p
        * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) (y - p))
      MeasureTheory.volume :=
    ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous
        (fun n => Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hg2sm n)).aestronglyMeasurable).congr
      (Eventually.of_forall (fun y =>
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε
          (Work.Spaces.mixed b a v) y)))
  have hK1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) (y - p)) ^ 2) :=
    (conv_shift_sq_integral_le (k := Work.FTS.StrongEps.Jker ρ ε)
      (Q := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w)
      (G := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u))
      hε0 hCl0 (Work.FTS.StrongEps.Jker_integrable hρ.moll hε0)
      (by
        have h1 : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) = 1 := by
          rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p|) = Work.FTS.StrongEps.Jker ρ ε
            from funext (fun p => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε p))]
          exact Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0
        rw [h1])
      (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
      hw0 hwm hwsh'
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg1sm).measurable
      (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable hρ.moll hε0
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg1sm) y)
      hI1).1
  have hK2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) (y - p)) ^ 2) :=
    (conv_shift_sq_integral_le (k := Work.FTS.StrongEps.Jker ρ ε)
      (Q := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w)
      (G := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v))
      hε0 hCl0 (Work.FTS.StrongEps.Jker_integrable hρ.moll hε0)
      (by
        have h1 : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) = 1 := by
          rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p|) = Work.FTS.StrongEps.Jker ρ ε
            from funext (fun p => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε p))]
          exact Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0
        rw [h1])
      (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
      hw0 hwm hwsh'
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg2sm).measurable
      (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable hρ.moll hε0
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg2sm) y)
      hI2).1
  have hX1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) (y - p))
      * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) y) :=
    integrable_cross_of_diag (μ := MeasureTheory.volume)
      (w := fun a' b' => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (a', b'))
      (A := fun a' b' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) ((a', b') - p))
      (B := fun a' b' => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) (a', b'))
      (Eventually.of_forall (fun q => hw0 q))
      (((hwm.aemeasurable.mul hconvm1.aemeasurable).mul
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg2sm).aemeasurable).aestronglyMeasurable)
      hK1 hI2
  have hX2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) y
      * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) (y - p))) :=
    integrable_cross_of_diag (μ := MeasureTheory.volume)
      (w := fun a' b' => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (a', b'))
      (A := fun a' b' => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) (a', b'))
      (B := fun a' b' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) ((a', b') - p))
      (Eventually.of_forall (fun q => hw0 q))
      (((hwm.aemeasurable.mul
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg1sm).aemeasurable).mul
        hconvm2.aemeasurable).aestronglyMeasurable)
      hI1 hK2
  -- the abstract transfer estimate
  have hpair := pairing_transfer_deriv hρ hLT hCl0 hw0 hwm hwsh hwsh' hε hg1sm hg2sm hC2
    hJ1 hJ2 hX1 hX2 hG1 hG2 hI1 hI2 hF2
  -- identification of the goal with the pairing form
  have e1 : Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
        (Work.Spaces.mixed b a v)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
          * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ
          * Work.Spaces.mixed b a v z θ := by
    rw [Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_fst (ρ := w)
      (A := Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
      (A' := Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u))
      (B := Work.Spaces.mixed b a v)
      (fun z θ h => Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε0
        (Work.FTS.EllipticEst.SmoothOpen.forall hu) h.1 h.2 b a)]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.wip_eq_flat]
  have e2 : Work.Coercivity.wip w (Work.Spaces.mixed b a u)
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
          * Work.Spaces.mixed b a u z θ
          * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v) z θ := by
    rw [Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_snd (ρ := w)
      (A := Work.Spaces.mixed b a u)
      (B := Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))
      (B' := Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v))
      (fun z θ h => Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε0
        (Work.FTS.EllipticEst.SmoothOpen.forall hv) h.1 h.2 b a)]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.wip_eq_flat]
  have q1 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a u))
      = Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * Work.Spaces.mixed b a u z θ ^ 2) := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.wip_eq_flat]
    congr 1
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => ?_))
    ring
  have q2 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a v) (Work.Spaces.mixed b a v))
      = Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * Work.Spaces.mixed b a v z θ ^ 2) := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.wip_eq_flat]
    congr 1
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => ?_))
    ring
  have q3 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a v)
        (Work.Spaces.mixed (b + 1) a v))
      = Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
          (Work.Spaces.Dz (Work.Spaces.mixed b a v))) := rfl
  have q4 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) v)
        (Work.Spaces.mixed b (a + 1) v))
      = Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
          (Work.Spaces.Dth (Work.Spaces.mixed b a v))) := by
    rw [hDthcongr]
  rw [e1, e2, q1, q2, q3, q4]
  refine hpair.trans ?_
  have hB20 := wip_self_nonneg hleaf (Work.Spaces.Dth (Work.Spaces.mixed b a v))
  have hA20 := wip_self_nonneg hleaf (Work.Spaces.Dz (Work.Spaces.mixed b a v))
  have hsd : Real.sqrt (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v)) y‖ ^ 2)
      ≤ 2 * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
            (Work.Spaces.Dz (Work.Spaces.mixed b a v)))
        + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
            (Work.Spaces.Dth (Work.Spaces.mixed b a v))) := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    calc Real.sqrt (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull
              (Work.Spaces.mixed b a v)) y‖ ^ 2)
        ≤ Real.sqrt (2 * Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
              (Work.Spaces.Dz (Work.Spaces.mixed b a v))
            + Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
              (Work.Spaces.Dth (Work.Spaces.mixed b a v))) := Real.sqrt_le_sqrt hF2le
      _ ≤ Real.sqrt (2 * Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
              (Work.Spaces.Dz (Work.Spaces.mixed b a v))) + Real.sqrt (Work.Coercivity.wip w
              (Work.Spaces.Dth (Work.Spaces.mixed b a v))
              (Work.Spaces.Dth (Work.Spaces.mixed b a v))) :=
          sqrt_add_le_aux (by linarith) hB20
      _ = Real.sqrt 2 * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
              (Work.Spaces.Dz (Work.Spaces.mixed b a v)))
            + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
              (Work.Spaces.Dth (Work.Spaces.mixed b a v))) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
              (Work.Spaces.Dz (Work.Spaces.mixed b a v)))
            + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
              (Work.Spaces.Dth (Work.Spaces.mixed b a v))) := by
          nlinarith [h2, Real.sqrt_nonneg (Work.Coercivity.wip w
            (Work.Spaces.Dz (Work.Spaces.mixed b a v)) (Work.Spaces.Dz (Work.Spaces.mixed b a v)))]
  have hstep : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * Work.Spaces.mixed b a v z θ ^ 2)
      + Real.sqrt (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v)) y‖ ^ 2)
      ≤ 2 * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            w z θ * Work.Spaces.mixed b a v z θ ^ 2)
          + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
              (Work.Spaces.Dz (Work.Spaces.mixed b a v)))
          + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
              (Work.Spaces.Dth (Work.Spaces.mixed b a v)))) := by
    have h5 := Real.sqrt_nonneg (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      w z θ * Work.Spaces.mixed b a v z θ ^ 2)
    have h6 := Real.sqrt_nonneg (Work.Coercivity.wip w (Work.Spaces.Dz (Work.Spaces.mixed b a v))
      (Work.Spaces.Dz (Work.Spaces.mixed b a v)))
    have h7 := Real.sqrt_nonneg (Work.Coercivity.wip w (Work.Spaces.Dth (Work.Spaces.mixed b a v))
      (Work.Spaces.Dth (Work.Spaces.mixed b a v)))
    linarith [hsd, h5, h6, h7, hA20, hB20]
  have hfac : (0 : ℝ) ≤ 100 * (Cl + 1) * Real.exp (4 * Cl) * ε
      * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * Work.Spaces.mixed b a u z θ ^ 2) := by
    have h1 : (0 : ℝ) ≤ 100 * (Cl + 1) * Real.exp (4 * Cl) := by positivity
    have h2 : (0 : ℝ) ≤ ε := le_of_lt hε0
    have h3 := Real.sqrt_nonneg (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      w z θ * Work.Spaces.mixed b a u z θ ^ 2)
    positivity
  nlinarith [hstep, hfac]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
