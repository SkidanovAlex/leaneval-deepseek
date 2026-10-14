import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logW_fderiv_integral_le
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsQuadSq` — the diagonal integrability of the mollified slot on the quadrant

For a leaf weight `w` and a profile `g` smooth on the open quadrant with `logW w · (logPull g)²`
integrable on the plane, the diagonal `w · (J_ε g)²` is integrable on the quadrant.  The
ingredient is `conv_shift_sq_integral_le` (the weighted `L²` Young inequality of the plane
convolution), transported to the quadrant by the log-coordinate substitution
(`JepsTransfer.lintegral_logW_sq_eq`).
-/

noncomputable section
open scoped Real Topology ENNReal ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `w · (J_ε g)²` is integrable on the open quadrant. -/
theorem jeps_quad_sq_integrable {ρ : ℝ × ℝ → ℝ} {w : ℝ → ℝ → ℝ} {g : Fn} {Cw ε α : ℝ} {a : ℕ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hCw : 0 ≤ Cw) (hε0 : 0 < ε)
    (hleaf : Work.FTS.TransportS.IsLeafW α a w)
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hwsh' : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hI : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2)) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2
        * (Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) ^ 2)
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
  have hcL : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hg
  have hkabs : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) ≤ 1 := by
    have h1 : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) = 1 := by
      rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p|) = Work.FTS.StrongEps.Jker ρ ε
        from funext (fun p => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε p))]
      exact Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0
    rw [h1]
  have hK : MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y - p)) ^ 2) :=
    (conv_shift_sq_integral_le (k := Work.FTS.StrongEps.Jker ρ ε)
      (Q := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w)
      (G := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      hε0 hCw (Work.FTS.StrongEps.Jker_integrable hρ.moll hε0) hkabs
      (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
      hw0 hwm hwsh' hcL.measurable
      (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
        hρ.moll hε0 hcL y) hI).1
  have hJepsPlane : MeasureTheory.Integrable (fun y : ℝ × ℝ =>
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.FTS.StrongEps.Jeps ρ ε g) y) ^ 2) :=
    hK.congr (Eventually.of_forall (fun y => by
      show Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y - p)) ^ 2
        = Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.Jeps ρ ε g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2
      rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε g y]))
  have hlinPlane : (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.FTS.StrongEps.Jeps ρ ε g) y) ^ 2))
      ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hJepsPlane
      (Eventually.of_forall (fun y => mul_nonneg (hw0 y) (sq_nonneg _)))]
    exact ENNReal.ofReal_ne_top
  have hgm : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull
      (Work.FTS.StrongEps.Jeps ρ ε g)) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous
      (fun n => Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hg n)).aemeasurable
  have hquadIter : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (w z θ
      * (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2)) ≠ ⊤ := by
    rw [← Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.lintegral_logW_sq_eq w
      (Work.FTS.StrongEps.Jeps ρ ε g) hw0 hwm hgm]
    exact hlinPlane
  have hquadProd : (∫⁻ q in Work.FTS.StrongEps.Quad, ENNReal.ofReal (w q.1 q.2
      * (Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) ^ 2)) ≠ ⊤ := by
    have hme : MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad
        = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      (Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (Set.Ioi 0) (Set.Ioo 0 (Real.pi / 2))).symm
    have hme1 : MeasureTheory.volume.restrict (Set.Ioi 0)
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
    have hme2 : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
        = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))
    have hmeasQ : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (w q.1 q.2
        * (Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) ^ 2))
        (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW
            hleaf).aemeasurable (Work.FTS.StrongEps.isOpen_Quad.measurableSet) |>.mul
          (((Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hg 0).continuousOn.pow 2).aemeasurable
            (Work.FTS.StrongEps.isOpen_Quad.measurableSet)))
    have hmeasQ0 : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (w q.1 q.2
        * (Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
      rw [← hme]; exact hmeasQ
    rw [hme]
    rw [MeasureTheory.lintegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal (w q.1 q.2
      * (Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) ^ 2)) hmeasQ0]
    rw [hme1, hme2]
    exact hquadIter
  refine ⟨?_, ?_⟩
  · exact ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW
        hleaf).mul
      ((Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hg 0).continuousOn.pow 2)).aestronglyMeasurable
      (Work.FTS.StrongEps.isOpen_Quad.measurableSet)
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal ?_]
    · exact lt_top_iff_ne_top.mpr hquadProd
    · refine (MeasureTheory.ae_restrict_mem
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet)).mono (fun q hq => ?_)
      exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf q.1
        ⟨hq.2.1.le, hq.2.2.le⟩) (sq_nonneg _)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
