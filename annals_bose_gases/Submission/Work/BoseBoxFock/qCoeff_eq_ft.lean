import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_chiLam_exp
import Submission.Work.BoseBoxFock.thetaFun_mul_psi_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock

/-- **The box `Λ(ℓ) = ℓ • unitCell` is the centred cube `acube ℓ`** (for `ℓ > 0`).

`corpusBox.boxL ℓ` is `ℓ • cell`, `cell` being the unit cube `[-1/2,1/2]³` of the corpus
`BoxData`; the centred cube `acube ℓ` is `{y | ∀ i, y i ∈ Icc (−ℓ/2) (ℓ/2)}`.  The two agree
because `y ∈ ℓ • unitCell ↔ ℓ⁻¹ • y ∈ unitCell ↔ ∀ i, ℓ⁻¹|y i| ≤ 1/2 ↔ ∀ i, |y i| ≤ ℓ/2`.

This is the dictionary between the (unit-cube based) corpus box and the (centred) box used by
`Work.BSKinetic.bsMean`/`bsQ`; it is what lets the `θ_Λ`-integral of a state supported in
`boxL ℓ` be read as `∫_{acube ℓ}`. -/
lemma corpusBox_boxL_eq_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ := by
  have hcancel : ∀ a : ℝ, ℓ * (ℓ⁻¹ * a) = a := by
    intro a; rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
  ext y
  rw [Work.BoseB4.BoxData.boxL, Work.BoseK15.corpusBox, Submission.BoseGases.mem_acube_iff]
  simp only [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ), Work.BoseB4.unitCell,
    Set.mem_ofPred_eq]
  constructor
  · intro h i
    have hi := h i
    simp only [PiLp.smul_apply, smul_eq_mul] at hi
    rw [abs_le] at hi
    rw [Set.mem_Icc]
    have hb := mul_le_mul_of_nonneg_left hi.1 hℓ.le
    have hc := mul_le_mul_of_nonneg_left hi.2 hℓ.le
    rw [hcancel] at hb hc
    constructor <;> nlinarith
  · intro h i
    have hi : y.ofLp i ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := h i
    rw [Set.mem_Icc] at hi
    rw [abs_le]
    simp only [PiLp.smul_apply, smul_eq_mul]
    constructor
    · have : ℓ * (-(1/2:ℝ)) ≤ ℓ * (ℓ⁻¹ * y.ofLp i) := by
        rw [hcancel]; nlinarith [hi.1]
      nlinarith [this]
    · have : ℓ * (ℓ⁻¹ * y.ofLp i) ≤ ℓ * (1/2:ℝ) := by
        rw [hcancel]; nlinarith [hi.2]
      nlinarith [this]

/-- **The left-hand side of `kinRow_lattice` is a box-Fourier coefficient of the windowed,
mean-free state.**  For smooth `ψ` supported in the box `boxL ℓ` and any momentum `k`, the
pairing of `ψ` with the corpus's localised plane wave
`qVec ℓ k = e^{ik·}χ_Λ − χ̂(ℓk)·1_Λ` equals the Fourier transform (at `k`) of
`bsWin ℓ 0 · bsQ ℓ 0 ψ = χ_Λ·(ψ − ℓ⁻³∫_{acube ℓ} ψ)`. -/
theorem qCoeff_eq_ft {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) (k : ℝ³) :
    qCoeff ℓ k ψ
      = ∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ) * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ) := by
  -- (1) The pointwise conjugation of the corpus mode.
  have hconj : ∀ z : ℝ³, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k z)
      = Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    intro z
    rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, map_sub, map_mul,
      Complex.conj_ofReal, map_mul, Complex.conj_ofReal]
    congr 2
    · rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]; congr 1; ring
    · by_cases h : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
        simp [Work.BoseB4.BoxData.thetaFun_apply, h]
  -- (2) Compact support and integrability of the pieces.
  have hpsi_cs : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (Work.BoseB4.BoxData.boxL_compact _ ℓ) (isClosed_tsupport ψ)
      hψsupp
  have hpsi_int : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z : ℂ)) :=
    (Complex.continuous_ofReal.comp hψ.continuous).integrable_of_hasCompactSupport
      (hpsi_cs.comp_left Complex.ofReal_zero)
  have hchiCs : HasCompactSupport
      (fun z : ℝ³ => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
    ((Work.BoseB4.BoxData.hasCompactSupport_chi _).comp_smul
      (inv_ne_zero (ne_of_gt hℓ))).comp_left Complex.ofReal_zero
  have hGcont : Continuous (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
    (Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg)).mul
      (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ))
  have hG_cs : HasCompactSupport (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) := hchiCs.mul_left
  have hGint : MeasureTheory.Integrable (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
    hGcont.integrable_of_hasCompactSupport hG_cs
  have hGpsi_int : MeasureTheory.Integrable (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ)) :=
    (hGcont.mul (Complex.continuous_ofReal.comp hψ.continuous)).integrable_of_hasCompactSupport
      hG_cs.mul_right
  have hind : MeasureTheory.Integrable (fun z : ℝ³ =>
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z) :=
    hpsi_int.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)
  have hpt_eq : (fun z : ℝ³ => ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
        * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z)
      = fun z : ℝ³ => ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ) := by
    funext z
    by_cases h : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem h, Work.BoseB4.BoxData.thetaFun_apply, if_pos h]; ring
    · rw [Set.indicator_of_notMem h, Work.BoseB4.BoxData.thetaFun_apply, if_neg h]; ring
  have htheta_int : MeasureTheory.Integrable (fun z : ℝ³ =>
      ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)) := by
    rw [← hpt_eq]; exact hind.const_mul _
  -- (3) Reduction of the left-hand side.
  have hL : qCoeff ℓ k ψ
      = (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ))
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k)
            * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z : ℝ) : ℂ) := by
    rw [Work.BoseBoxFock.qCoeff]
    rw [show (∫ z, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k z) * (ψ z : ℂ))
        = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ z) * (ψ z : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hconj])]
    rw [show (∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ z) * (ψ z : ℂ))
        = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ)
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)]
    rw [integral_sub hGpsi_int htheta_int, thetaFun_mul_psi_integral hψ hψsupp k]
  -- (4) Reduction of the right-hand side.
  have hm_eq : Work.BSKinetic.bsMean ℓ 0 ψ
      = (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, ψ z := by
    simp [Work.BSKinetic.bsMean]
  have hbsq : ∀ z : ℝ³, ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)
      = (ψ z : ℂ) - ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ) := by
    intro z; simp [Work.BSKinetic.bsQ]
  have hwin : ∀ z : ℝ³, ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)
      = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) := by
    intro z
    simp [Work.BSKinetic.bsWin, Submission.BoseGases.chiScale, Work.BoseB4.BoxData.chiLam,
      Work.BoseK15.corpusBox]
  have hl3m : ℓ ^ 3 * Work.BSKinetic.bsMean ℓ 0 ψ
      = ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z := by
    rw [hm_eq, ← corpusBox_boxL_eq_acube hℓ, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
  have hR : (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)
          * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ))
      = (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ))
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k)
            * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z : ℝ) : ℂ) := by
    rw [show (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
          * ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ)
          * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ))
        = ∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * ((ψ z : ℂ) - ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hwin, hbsq])]
    rw [show (∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * ((ψ z : ℂ) - ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ)))
        = ∫ z, (Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * (ψ z : ℂ)
          - Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * ((Work.BSKinetic.bsMean ℓ 0 ψ : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)]
    rw [integral_sub hGpsi_int (hGint.mul_const _), integral_mul_const,
      integral_chiLam_exp hℓ k]
    congr 1
    rw [← Complex.ofReal_mul,
      show ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) * Work.BSKinetic.bsMean ℓ 0 ψ
          = Work.BoseK15.corpusBox.hatChi (ℓ • k)
            * (ℓ ^ 3 * Work.BSKinetic.bsMean ℓ 0 ψ) from by ring, hl3m]
  rw [hL, hR]

end Work.BoseBoxFock
