import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kinRow_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The box `θ`-integral identity `∫ χ̂(ℓk)·θ_Λ·ψ = χ̂(ℓk)·∫_{boxL ℓ}ψ` for an arbitrary
`BoxData` and an arbitrary state `ψ`: no support or regularity hypothesis is needed, because
`θ_Λ = 1_{boxL ℓ}` pointwise.  This is `Work.BoseBoxFock.thetaFun_mul_psi_integral` with its
(unused) hypotheses dropped. -/
lemma thetaFun_mul_psi_integral_gen (B : Work.BoseB4.BoxData) {ℓ : ℝ}
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (k : EuclideanSpace ℝ (Fin 3)) :
    ∫ z, ((B.hatChi (ℓ • k) : ℝ) : ℂ) * B.thetaFun ℓ z * (ψ z : ℂ)
      = ((B.hatChi (ℓ • k) * ∫ z in B.boxL ℓ, ψ z : ℝ) : ℂ) := by
  set c : ℝ := B.hatChi (ℓ • k) with hc
  have hsmeas : MeasurableSet (B.boxL ℓ) := B.boxL_measurableSet ℓ
  have hpt : ∀ z, ((c : ℝ) : ℂ) * B.thetaFun ℓ z * (ψ z : ℂ)
      = (c : ℂ) * (B.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z := by
    intro z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ B.boxL ℓ
    · rw [if_pos hz, Set.indicator_of_mem hz]; ring
    · rw [if_neg hz, Set.indicator_of_notMem hz]; ring
  calc ∫ z, ((c : ℝ) : ℂ) * B.thetaFun ℓ z * (ψ z : ℂ)
      = ∫ z, (c : ℂ) * (B.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (c : ℂ) * ∫ z, (B.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z :=
        MeasureTheory.integral_const_mul (c : ℂ) _
    _ = (c : ℂ) * ∫ z in B.boxL ℓ, (ψ z : ℂ) := by
        rw [MeasureTheory.integral_indicator hsmeas]
    _ = (c : ℂ) * ((∫ z in B.boxL ℓ, ψ z : ℝ) : ℂ) := by
        congr 1
        exact integral_ofReal
    _ = ((c * ∫ z in B.boxL ℓ, ψ z : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul]

/-- `θ_Λ·ψ` is integrable (times a constant) for an arbitrary state: it is the indicator of the
box of a continuous function, and the box is compact. -/
lemma integrable_const_thetaFun_mul {ℓ : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : Continuous ψ) (c : ℂ) :
    Integrable (fun z => c * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)) := by
  have hmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hOn : IntegrableOn (fun z => (ψ z : ℂ)) (Work.BoseK15.corpusBox.boxL ℓ) :=
    (Complex.continuous_ofReal.comp hψ).continuousOn.integrableOn_compact
      (Work.BoseB4.BoxData.boxL_compact _ ℓ)
  have hInd : Integrable
      (fun z => (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z) :=
    (integrable_indicator_iff hmeas).mpr hOn
  refine (hInd.const_mul c).congr (Filter.Eventually.of_forall fun z => ?_)
  show c * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z
      = c * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [if_pos hz, Set.indicator_of_mem hz]; ring
  · rw [if_neg hz, Set.indicator_of_notMem hz]; ring

/-- **Per-fibre box-Fourier dictionary, no support hypothesis.**  For `ℓ > 0` and smooth `ψ`
(no support hypothesis) and *any* momentum `k`: the corpus's box-Fourier coefficient
`qCoeff ℓ k ψ = ∫_z conj(qVec ℓ k z) · ψ z` equals the `p`-convention Fourier transform at `k` of
the windowed mean-free state `winState ℓ ψ = χ_Λ·(ψ − ℓ⁻³∫_{acube ℓ} ψ)`.

This is `Work.BoseBoxFock.qCoeff_eq_ft` (⟶ `qCoeff_eq_kinFT`) with the hypothesis
`tsupport ψ ⊆ boxL ℓ` dropped: both sides only see `ψ` on `boxL ℓ = acube ℓ`, and continuous `ψ`
is integrable on that compact box.  Needed for fibres of a globally defined state, which are
smooth but not compactly supported. -/
theorem qCoeff_eq_kinFT_general {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.qCoeff ℓ k ψ
      = Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) k := by
  set B := Work.BoseK15.corpusBox with hB
  -- (1) The pointwise conjugation of the corpus mode.
  have hconj : ∀ z : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (B.qVec ℓ k z)
      = Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))) * ((B.chiLam ℓ z : ℝ) : ℂ)
        - ((B.hatChi (ℓ • k) : ℝ) : ℂ) * B.thetaFun ℓ z := by
    intro z
    rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, map_sub, map_mul,
      Complex.conj_ofReal, map_mul, Complex.conj_ofReal]
    congr 2
    · rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]; congr 1; ring
    · by_cases h : z ∈ B.boxL ℓ <;> simp [Work.BoseB4.BoxData.thetaFun_apply, h]
  -- (2) Integrability of the pieces (everything is compactly supported or bounded on the box).
  have hchiCs : HasCompactSupport
      (fun z : EuclideanSpace ℝ (Fin 3) => ((B.chiLam ℓ z : ℝ) : ℂ)) :=
    ((Work.BoseB4.BoxData.hasCompactSupport_chi _).comp_smul
      (inv_ne_zero (ne_of_gt hℓ))).comp_left Complex.ofReal_zero
  have hGcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))) * ((B.chiLam ℓ z : ℝ) : ℂ)) :=
    (Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg)).mul
      (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont B ℓ))
  have hG_cs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))) * ((B.chiLam ℓ z : ℝ) : ℂ)) :=
    hchiCs.mul_left
  have hGint : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))) * ((B.chiLam ℓ z : ℝ) : ℂ)) :=
    hGcont.integrable_of_hasCompactSupport hG_cs
  have hGpsi_int : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
      * ((B.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ)) :=
    (hGcont.mul (Complex.continuous_ofReal.comp hψ.continuous)).integrable_of_hasCompactSupport
      hG_cs.mul_right
  have htheta_int : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((B.hatChi (ℓ • k) : ℝ) : ℂ) * B.thetaFun ℓ z * (ψ z : ℂ)) := by
    rw [hB]
    exact integrable_const_thetaFun_mul hψ.continuous _
  -- (3) Reduction of the left-hand side.
  have hL : qCoeff ℓ k ψ
      = (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ))
        - ((B.hatChi (ℓ • k) * ∫ z in B.boxL ℓ, ψ z : ℝ) : ℂ) := by
    rw [Work.BoseBoxFock.qCoeff]
    rw [show (∫ z, (starRingEnd ℂ) (B.qVec ℓ k z) * (ψ z : ℂ))
        = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((B.chiLam ℓ z : ℝ) : ℂ)
            - ((B.hatChi (ℓ • k) : ℝ) : ℂ)
              * B.thetaFun ℓ z) * (ψ z : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hconj])]
    rw [show (∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((B.chiLam ℓ z : ℝ) : ℂ)
            - ((B.hatChi (ℓ • k) : ℝ) : ℂ)
              * B.thetaFun ℓ z) * (ψ z : ℂ))
        = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((B.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ)
            - ((B.hatChi (ℓ • k) : ℝ) : ℂ)
              * B.thetaFun ℓ z * (ψ z : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)]
    rw [integral_sub hGpsi_int htheta_int, thetaFun_mul_psi_integral_gen B k]
  -- (4) Reduction of the right-hand side.
  have hm_eq : Work.BSKinetic.bsMean ℓ 0 ψ
      = (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, ψ z := by
    simp [Work.BSKinetic.bsMean]
  have hbsq : ∀ z : EuclideanSpace ℝ (Fin 3),
      ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)
      = (ψ z : ℂ) - ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ) := by
    intro z; simp [Work.BSKinetic.bsQ]
  have hwin : ∀ z : EuclideanSpace ℝ (Fin 3),
      ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)
      = ((B.chiLam ℓ z : ℝ) : ℂ) := by
    intro z
    rw [hB]
    simp [Work.BSKinetic.bsWin, Submission.BoseGases.chiScale, Work.BoseB4.BoxData.chiLam,
      Work.BoseK15.corpusBox]
  have hl3m : ℓ ^ 3 * Work.BSKinetic.bsMean ℓ 0 ψ
      = ∫ z in B.boxL ℓ, ψ z := by
    rw [hm_eq, ← corpusBox_boxL_eq_acube hℓ, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
  have hRbs : (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)
          * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ))
      = (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ))
        - ((B.hatChi (ℓ • k) * ∫ z in B.boxL ℓ, ψ z : ℝ) : ℂ) := by
    rw [show (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)
          * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ))
        = ∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ)
            * ((ψ z : ℂ) - ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hwin, hbsq])]
    rw [show (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ)
            * ((ψ z : ℂ) - ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ)))
        = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ)
          - Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ)
            * ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)]
    rw [integral_sub hGpsi_int (hGint.mul_const _), integral_mul_const,
      integral_chiLam_exp hℓ k]
    congr 1
    rw [← Complex.ofReal_mul,
      show ℓ ^ 3 * B.hatChi (ℓ • k) * Work.BSKinetic.bsMean ℓ 0 ψ
          = B.hatChi (ℓ • k) * (ℓ ^ 3 * Work.BSKinetic.bsMean ℓ 0 ψ) from by ring, hl3m]
  have hR : Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) k
      = (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((B.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ))
        - ((B.hatChi (ℓ • k) * ∫ z in B.boxL ℓ, ψ z : ℝ) : ℂ) := by
    rw [Submission.BoseGases.kinFT]
    rw [show (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * Work.BoseBoxFock.winState ℓ ψ z)
        = ∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BSKinetic.bsWin ℓ 0 z : ℂ)) * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by
        rw [← winState_eq ℓ ψ]; ring)]
    exact hRbs
  rw [hL, hR]

end Work.BoseBoxFock
