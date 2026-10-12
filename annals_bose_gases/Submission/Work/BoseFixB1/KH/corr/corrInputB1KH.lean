import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1S.corr.corrMeanSqKH
import Submission.Work.BoseFixB1S.corr.integrableBSWCutKH
import Submission.Work.BoseFixB1S.corr.measurableBoxMeanKH
import Submission.Work.BoseFixB1S.corrCutWordsSharp
import Submission.Work.BoseFixB1S.corrMarg.integrable_and_marginal_chiB
import Submission.Work.BoseFixB1S.corrPlanchMarg
import Submission.Work.BoseFixB1S.fsXpLogSmall
import Submission.Work.BoseFixB1S.kineticCruxParsed
import Submission.Work.BoseFixR.Kin.Expand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.KH.corr.corrInputB1KH`

The intersection-mean correction `Work.BoseFixB1S.CorrInput v` (the `(E2)`+`(E3)` mean-mismatch
step of `FINDING_unprojected_route_B.md`), proved by the assembly
`cruxCorrB1_of_pieces` from the six pieces `CutWords`, `MeanSq`, `Marginal`, `Arith`, `ChiL2`,
`PlanchMarg`.  The bookkeeping (sections 1--3 below, the pointwise mean-shift step `crux_pt`,
the abbreviations `corrSt`/`corrBC`/`corrQ`/... and the assembly theorem
`cruxCorrB1_of_pieces`) is reproduced here so that this module is independent of the way the
sibling skeleton `Submission.Work.BoseFixB1S.cruxCorrB1` is being re-organised; the six pieces
are imported from their own modules.
-/

noncomputable section
open MeasureTheory
open scoped Real Topology BigOperators ContDiff ENNReal

namespace Work.BoseFixB1.KH.corr

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Submission.BoseGases

/-! ## 1.  Scalar linearity of `bsPsi` in the squared norm, and of `bsW` -/

/-- A real constant pulls out of the `p`-transform of a state. -/
lemma bsPsi_const_mul {w : E3 → ℝ} (c : ℝ) (p : E3) :
    Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p
      = (c : ℂ) * Work.BSKinetic.Decomp.bsPsi w p := by
  have h₁ : (fun z : E3 => ((c * w z : ℝ) : ℂ)) = fun z => (c : ℂ) * (w z : ℂ) := by
    funext z; push_cast; ring
  simp only [Work.BSKinetic.Decomp.bsPsi]
  rw [h₁]
  simp only [Submission.BoseGases.kinFT]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

/-- A real constant pulls out of the squared norm of the `p`-transform. -/
lemma bsPsi_const_mul_normSq {w : E3 → ℝ} (c : ℝ) (p : E3) :
    ‖Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p‖ ^ 2
      = c ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi w p‖ ^ 2 := by
  rw [bsPsi_const_mul, norm_mul, mul_pow]
  have hc : ‖((c : ℝ) : ℂ)‖ ^ 2 = c ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  rw [hc]

/-- **Scalar linearity of `bsW`.** -/
lemma bsW_const_mul {F : ℝ → ℝ} {w : E3 → ℝ} (c : ℝ) :
    Work.BSKinetic.Decomp.bsW F (fun z => c * w z)
      = c ^ 2 * Work.BSKinetic.Decomp.bsW F w := by
  rw [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsW,
    show (fun p : E3 => F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p‖ ^ 2)
        = fun p : E3 => c ^ 2 * (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi w p‖ ^ 2) from by
      funext p; rw [bsPsi_const_mul_normSq]; ring,
    MeasureTheory.integral_const_mul]

/-- The same, in the `F²`-weighted form (the one entering the cross-term estimate). -/
lemma Fsq_bsPsi_const_mul {F : ℝ → ℝ} {w : E3 → ℝ} (c : ℝ) :
    (∫ p : E3, F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p‖ ^ 2)
      = c ^ 2 * (∫ p : E3, F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi w p‖ ^ 2) := by
  rw [show (fun p : E3 => F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p‖ ^ 2)
        = fun p : E3 => c ^ 2 * (F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi w p‖ ^ 2) from by
      funext p; rw [bsPsi_const_mul_normSq]; ring,
    MeasureTheory.integral_const_mul]

/-- The `F²`-weighted integrability transfers to a scaled state. -/
lemma integrable_Fsq_bsPsi_const_mul {F : ℝ → ℝ} {w : E3 → ℝ} (c : ℝ)
    (h : MeasureTheory.Integrable (fun p : E3 => F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi w p‖ ^ 2)) :
    MeasureTheory.Integrable
      (fun p : E3 => F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p‖ ^ 2) := by
  rw [show (fun p : E3 => F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi (fun z => c * w z) p‖ ^ 2)
        = fun p : E3 => c ^ 2 * (F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi w p‖ ^ 2) from by
      funext p; rw [bsPsi_const_mul_normSq]; ring]
  exact h.const_mul (c ^ 2)

/-! ## 2.  The `L²`-based bound for the bilinear form -/

/-- **Cauchy–Schwarz for `bsWBilin`**, with the `F²`-weight on the first slot and the plain `L²`
weight on the second. -/
lemma bsWBilin_le_sqrt {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (hFc : Continuous F) {a b : E3 → ℝ}
    (had : ContDiff ℝ (⊤ : ENat) a) (hac : HasCompactSupport a)
    (hbd : ContDiff ℝ (⊤ : ENat) b) (hbc : HasCompactSupport b)
    (hFb : MeasureTheory.Integrable (fun p : E3 => F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2)) :
    |Work.BoseFixR.bsWBilin F a b|
      ≤ Real.sqrt (∫ p : E3, F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2)
        * Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2) := by
  have hconta : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi a p) :=
    Work.BSKinetic.Decomp.continuous_bsPsi had hac
  have hcontb : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi b p) :=
    Work.BSKinetic.Decomp.continuous_bsPsi hbd hbc
  have hbmeas : AEStronglyMeasurable (fun p : E3 => F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) :=
    (((hFc.comp continuous_norm).mul hcontb.norm)).aestronglyMeasurable
  have hameas : AEStronglyMeasurable (fun p : E3 => ‖Work.BSKinetic.Decomp.bsPsi a p‖) :=
    hconta.norm.aestronglyMeasurable
  have hbsq : MeasureTheory.Integrable
      (fun p : E3 => (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) ^ 2) := by
    refine hFb.congr (Filter.Eventually.of_forall fun p => ?_)
    change F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2
      = (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) ^ 2
    ring
  have hasq : MeasureTheory.Integrable (fun p : E3 => ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2) := by
    simpa only [Work.BSKinetic.Decomp.bsPsi] using Work.BSKinetic.integrable_kinFT_sq a had hac
  have hbmem : MemLp (fun p : E3 => F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) 2 :=
    (memLp_two_iff_integrable_sq hbmeas).mpr hbsq
  have hamem : MemLp (fun p : E3 => ‖Work.BSKinetic.Decomp.bsPsi a p‖) 2 :=
    (memLp_two_iff_integrable_sq hameas).mpr hasq
  have hprod_int : MeasureTheory.Integrable (fun p : E3 =>
      (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) * ‖Work.BSKinetic.Decomp.bsPsi a p‖) :=
    hbmem.integrable_mul hamem
  have hcont_re : Continuous (fun p : E3 =>
      (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re) :=
    Complex.continuous_re.comp (hconta.mul (continuous_star.comp hcontb))
  have hbd_int : MeasureTheory.Integrable (fun p : E3 =>
      F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re) := by
    refine hprod_int.mono' ?_ ?_
    · exact (((hFc.comp continuous_norm).mul hcont_re)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF ‖p‖), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hF ‖p‖)
      calc |(Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re|
          ≤ ‖Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖Work.BSKinetic.Decomp.bsPsi b p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ := by
            rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj, mul_comm]
  have hmain : |Work.BoseFixR.bsWBilin F a b| ≤ ∫ p : E3,
      (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) * ‖Work.BSKinetic.Decomp.bsPsi a p‖ := by
    rw [Work.BoseFixR.bsWBilin]
    have h2 : ‖(∫ p : E3,
          F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re : ℝ)‖
        ≤ ∫ p : E3,
          ‖(F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re : ℝ)‖ :=
      MeasureTheory.norm_integral_le_integral_norm (μ := volume)
        (f := fun p : E3 => F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re)
    simp only [Real.norm_eq_abs] at h2
    refine le_trans h2 ?_
    refine MeasureTheory.integral_mono hbd_int.abs hprod_int (fun p => ?_)
    rw [abs_mul, abs_of_nonneg (hF ‖p‖), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hF ‖p‖)
    calc |(Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re|
        ≤ ‖Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)‖ :=
          Complex.abs_re_le_norm _
      _ = ‖Work.BSKinetic.Decomp.bsPsi b p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ := by
          rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj, mul_comm]
  have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hbmem hamem
  have hvalb : (∫ p : E3, (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) ^ 2)
      = ∫ p : E3, F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) ^ 2
      = F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2
    ring
  rw [hvalb] at hcs
  refine hmain.trans ?_
  refine le_trans (le_abs_self _) ?_
  rw [show (fun p : E3 => (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) * ‖Work.BSKinetic.Decomp.bsPsi a p‖)
      = fun p : E3 => (fun q : E3 => F ‖q‖ * ‖Work.BSKinetic.Decomp.bsPsi b q‖) p *
          (fun q : E3 => ‖Work.BSKinetic.Decomp.bsPsi a q‖) p from rfl]
  exact hcs

/-! ## 3.  The parameter-free window bound, the pairing integrability and the box-mean algebra -/

/-- `chiScale` is uniformly bounded by the inverse square root of the bump's `L²`-mass. -/
lemma chiScale_sq_le (ℓ : ℝ) (z : E3) :
    (Submission.BoseGases.chiScale ℓ z) ^ 2 ≤ (Submission.BoseGases.chiNormSq)⁻¹ := by
  rw [Submission.BoseGases.chiScale, Submission.BoseGases.chi, div_pow,
    Real.sq_sqrt (le_of_lt Submission.BoseGases.chiNormSq_pos)]
  have h0 : 0 ≤ Submission.BoseGases.chiBase ((ℓ⁻¹) • z) := Submission.BoseGases.chiBase_nonneg _
  have h1 : Submission.BoseGases.chiBase ((ℓ⁻¹) • z) ≤ 1 := Submission.BoseGases.chiBase_le_one _
  have hsq : (Submission.BoseGases.chiBase ((ℓ⁻¹) • z)) ^ 2 ≤ 1 := by nlinarith
  rw [div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right hsq
    (inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos))

/-- The `fsKinCoeff`-weighted pairing integrand of two smooth compactly supported states is
integrable. -/
lemma integrable_fsKinCoeff_cross {c : ℝ} {a b : E3 → ℝ}
    (had : ContDiff ℝ (⊤ : ENat) a) (hac : HasCompactSupport a)
    (hbd : ContDiff ℝ (⊤ : ENat) b) (hbc : HasCompactSupport b) :
    MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re) := by
  have hFc : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
    simp only [Submission.BoseGases.fsKinCoeff]; fun_prop
  have hca : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi a p) :=
    Work.BSKinetic.Decomp.continuous_bsPsi had hac
  have hcb : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi b p) :=
    Work.BSKinetic.Decomp.continuous_bsPsi hbd hbc
  have hinta := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) had hac
  have hintb := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) hbd hbc
  have hdom : MeasureTheory.Integrable (fun p : E3 =>
      (Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
        + Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2) :=
    (hinta.add hintb).div_const 2
  refine hdom.mono' ?_ ?_
  · exact ((hFc.comp continuous_norm).mul
      (Complex.continuous_re.comp (hca.mul (continuous_star.comp hcb)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    have hFnn : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ := Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
    have ham : |(Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re|
        ≤ ‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ := by
      calc |(Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re|
          ≤ ‖Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ := by
            rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hFnn]
    have hgm : ‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖
        ≤ (‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2 + ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖Work.BSKinetic.Decomp.bsPsi a p‖ - ‖Work.BSKinetic.Decomp.bsPsi b p‖)]
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          |(Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re|
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
            (‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) :=
          mul_le_mul_of_nonneg_left ham hFnn
      _ ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2 + ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hgm hFnn
      _ = (Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
            + Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2 := by
          ring

/-- The box mean of `g − c` is the box mean of `g` minus `c`, for a box of nonzero volume. -/
lemma boxMean_sub_const {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3} {g : E3 → ℝ}
    (hg : Continuous g) {c : ℝ} (hV : Work.SmallBoxSliding.boxMass ℓ d u ≠ 0) :
    (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        (∫ z in Submission.BoseGases.dlBox ℓ d u, (g z - c))
      = (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          (∫ z in Submission.BoseGases.dlBox ℓ d u, g z) - c := by
  have hms : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hfin : (volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
    Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
  have hcp : IsCompact (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u
  have hgi : MeasureTheory.IntegrableOn g (Submission.BoseGases.dlBox ℓ d u) :=
    hg.continuousOn.integrableOn_compact hcp
  have hci : MeasureTheory.IntegrableOn (fun _ : E3 => c) (Submission.BoseGases.dlBox ℓ d u) :=
    MeasureTheory.integrableOn_const hfin.ne (by simp)
  have hsub : (∫ z in Submission.BoseGases.dlBox ℓ d u, (g z - c))
      = (∫ z in Submission.BoseGases.dlBox ℓ d u, g z)
        - c * Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [MeasureTheory.integral_sub hgi hci,
      show (∫ z in Submission.BoseGases.dlBox ℓ d u, c) = c * Work.SmallBoxSliding.boxMass ℓ d u from by
        rw [MeasureTheory.setIntegral_const,
          ← Work.SmallBoxSliding.boxMass_eq_measureReal, smul_eq_mul, mul_comm]]
  rw [hsub, div_eq_mul_inv]
  field_simp
  try ring

/-! ## 4.  The three delegated pieces, as predicates -/

/-- The conclusion of `Work.BoseFixB1S.corrCutWordsSharp` at `v`. -/
def CutWords (v : E3 → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : E3,
      MeasureTheory.Integrable (fun p : E3 =>
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
      ∧ (Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z)
          ≤ C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
      ∧ ((∫ p : E3,
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
                ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
                  Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
          ≤ C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)

/-- The conclusion of `Work.BoseFixB1S.corrMeanSq` at `v`. -/
def MeanSq (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
        MeasureTheory.Integrable (fun u : E3 =>
            ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
              ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
        ∧ ((∫ u : E3,
              ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
            ≤ C * (1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
                    + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|) ^ 3
                * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
                * (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (w z) ^ 2))

/-- The conclusion of `Work.BoseFixB1S.corrMarginal` at `v`. -/
def Marginal (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
      MeasureTheory.Integrable (fun u : E3 =>
          Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * w z))
      ∧ MeasureTheory.Integrable (fun u : E3 =>
          Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (w z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                (∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z'))))
      ∧ MeasureTheory.Integrable (fun u : E3 =>
          ∫ z : E3,
            (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) ^ 2 * (w z) ^ 2)
      ∧ (∫ u : E3, ∫ z : E3,
            (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) ^ 2 * (w z) ^ 2)
        = (∫ z : E3,
            (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2 * (w z) ^ 2)

/-! ## 5.  The pointwise mean-shift step -/

/-- **(PT)** Pointwise mean shift: the sliding-box-mean state is dominated by the flat-mean state,
plus the box-mean square and the bilinear cross term (in the `L²`-normalised form used by the
`u`-integration). -/
lemma crux_pt {ℓ d κ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {g : E3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (u : E3) {Kq Ke : ℝ} (hKq : 0 ≤ Kq)
    (hQ : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z => Submission.BoseGases.chiB ℓ d u z) ≤ Kq)
    (hE : (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z => Submission.BoseGases.chiB ℓ d u z) p‖ ^ 2) ≤ Ke)
    (hEint : MeasureTheory.Integrable (fun p : E3 => (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z => Submission.BoseGases.chiB ℓ d u z) p‖ ^ 2))
    (c0 : ℝ) :
    Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z => Submission.BoseGases.chiB ℓ d u z *
          (g z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            (∫ z' in Submission.BoseGases.dlBox ℓ d u, g z')))
      ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
          (fun z => Submission.BoseGases.chiB ℓ d u z * (g z - c0))
        + Kq * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            (∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0))) ^ 2
        + 2 * (|(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
                (∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0))| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z => Submission.BoseGases.chiB ℓ d u z * (g z - c0)) p‖ ^ 2)) := by
  set χ : E3 → ℝ := Submission.BoseGases.chiB ℓ d u with hχdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set J : ℝ := ∫ z' in Submission.BoseGases.dlBox ℓ d u, g z' with hJdef
  set Jt : ℝ := ∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0) with hJtdef
  set bc : ℝ := (1 / V) * J with hbcdef
  set bm : ℝ := (1 / V) * Jt with hbmdef
  have hχd : ContDiff ℝ (⊤ : ENat) χ := by
    rw [hχdef]; exact Work.SmallBoxTBWord.contDiff_chiB hℓ hd u
  have hχc : HasCompactSupport χ := by
    rw [hχdef]; exact Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u
  have hgtd : ContDiff ℝ (⊤ : ENat) (fun z => g z - c0) := hg.sub contDiff_const
  have hFnn : ∀ r : ℝ, 0 ≤ Submission.BoseGases.fsKinCoeff κ r :=
    fun r => Submission.BoseGases.fsKinCoeff_nonneg κ r
  have hFcont : Continuous (Submission.BoseGases.fsKinCoeff κ) := by
    unfold Submission.BoseGases.fsKinCoeff; fun_prop
  by_cases hV0 : V = 0
  · -- the window vanishes on a null box
    have hχ0 : χ = 0 := by
      rw [hχdef]
      refine Work.UBBInputs8.A.chiB_eq_zero_of_volume_dlBox_eq_zero hℓ hd u ?_
      have hlt := Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
      rw [hVdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def] at hV0
      rcases (ENNReal.toReal_eq_zero_iff _).mp hV0 with h' | h'
      · exact h'
      · exact absurd h' hlt.ne
    have hst : (fun z => χ z * (g z - bc)) = fun z => χ z * (g z - c0) := by
      funext z; rw [hχ0]; simp
    have hsq0 : (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
        (fun z => χ z * (g z - c0)) p‖ ^ 2) = 0 := by
      have hz : (fun z : E3 => χ z * (g z - c0)) = fun _ : E3 => (0 : ℝ) := by
        funext z; rw [hχ0]; simp
      rw [hz]
      simp [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]
    have hbm0 : bm = 0 := by rw [hbmdef, hV0, div_zero, zero_mul]
    rw [hst, hbm0, hsq0, Real.sqrt_zero]
    linarith [le_refl (Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
      (fun z => χ z * (g z - c0)))]
  · -- the genuine case
    have hVbox : Work.SmallBoxSliding.boxMass ℓ d u ≠ 0 := by rwa [hVdef] at hV0
    have hbmbc : bm = bc - c0 := by
      rw [hbmdef, hbcdef, hJtdef, hJdef, hVdef]
      exact boxMean_sub_const hℓ hd hg.continuous hVbox
    have hstate : (fun z => χ z * (g z - bc)) = fun z => χ z * (g z - c0) + (-(bc - c0)) * χ z := by
      funext z; ring
    have hξd : ContDiff ℝ (⊤ : ENat) (fun z => χ z * (g z - c0)) := hχd.mul hgtd
    have hξc : HasCompactSupport (fun z => χ z * (g z - c0)) := hχc.mul_right
    have hbd : ContDiff ℝ (⊤ : ENat) (fun z => (-(bc - c0)) * χ z) := contDiff_const.mul hχd
    have hbcsh : HasCompactSupport (fun z => (-(bc - c0)) * χ z) := HasCompactSupport.mul_left hχc
    have hi1 : MeasureTheory.Integrable (fun p : E3 =>
        Submission.BoseGases.fsKinCoeff κ ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z => χ z * (g z - c0)) p‖ ^ 2) :=
      Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq hξd hξc
    have hi2 : MeasureTheory.Integrable (fun p : E3 =>
        Submission.BoseGases.fsKinCoeff κ ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z => (-(bc - c0)) * χ z) p‖ ^ 2) :=
      Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq hbd hbcsh
    have hi3 : MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff κ ‖p‖ *
        (Work.BSKinetic.Decomp.bsPsi (fun z => χ z * (g z - c0)) p *
          star (Work.BSKinetic.Decomp.bsPsi (fun z => (-(bc - c0)) * χ z) p)).re) :=
      integrable_fsKinCoeff_cross hξd hξc hbd hbcsh
    have hexp := Work.BoseFixR.bsW_add hξd hξc hbd hbcsh hi1 hi2 hi3
    have hself : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z => (-(bc - c0)) * χ z)
        = (bc - c0) ^ 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ := by
      rw [bsW_const_mul]; ring
    have hFb : MeasureTheory.Integrable (fun p : E3 =>
        (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z => (-(bc - c0)) * χ z) p‖ ^ 2) :=
      integrable_Fsq_bsPsi_const_mul (-(bc - c0)) hEint
    have hbound : |Work.BoseFixR.bsWBilin (Submission.BoseGases.fsKinCoeff κ)
          (fun z => χ z * (g z - c0)) (fun z => (-(bc - c0)) * χ z)|
        ≤ |bc - c0| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z => χ z * (g z - c0)) p‖ ^ 2) := by
      have hble := bsWBilin_le_sqrt (F := Submission.BoseGases.fsKinCoeff κ) hFnn hFcont
        hξd hξc hbd hbcsh hFb
      have hFbval : (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z => (-(bc - c0)) * χ z) p‖ ^ 2)
          = (bc - c0) ^ 2 * (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
              ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2) := by
        rw [Fsq_bsPsi_const_mul (F := Submission.BoseGases.fsKinCoeff κ) (w := χ) (-(bc - c0)),
          neg_sq]
      rw [hFbval] at hble
      have hEnn : (0 : ℝ) ≤ ∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2 :=
        integral_nonneg fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have h1 : Real.sqrt ((bc - c0) ^ 2 * (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2)) ≤ |bc - c0| * Real.sqrt Ke := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (abs_nonneg _)
      exact le_trans hble (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _))
    have hQ' : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ ≤ Kq := hQ
    have hQnn : (0 : ℝ) ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ :=
      integral_nonneg fun p => mul_nonneg (hFnn _) (sq_nonneg _)
    have hKq2 : (bc - c0) ^ 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ
        ≤ Kq * (bc - c0) ^ 2 := by
      rw [mul_comm Kq]
      exact mul_le_mul_of_nonneg_left hQ' (sq_nonneg _)
    have hcr2 : 2 * Work.BoseFixR.bsWBilin (Submission.BoseGases.fsKinCoeff κ)
          (fun z => χ z * (g z - c0)) (fun z => (-(bc - c0)) * χ z)
        ≤ 2 * (|bc - c0| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z => χ z * (g z - c0)) p‖ ^ 2)) := by
      have h1 : Work.BoseFixR.bsWBilin (Submission.BoseGases.fsKinCoeff κ)
          (fun z => χ z * (g z - c0)) (fun z => (-(bc - c0)) * χ z)
          ≤ |bc - c0| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z => χ z * (g z - c0)) p‖ ^ 2) := le_trans (le_abs_self _) hbound
      linarith only [h1]
    rw [hstate, hexp, hself]
    have hbm' : (bc - c0) = bm := hbmbc.symm
    rw [hbm'] at hKq2 hcr2 ⊢
    linarith [hKq2, hcr2]

/-! ## 6.  The three further helper lemmas, as predicates, and the assembly -/

/-- `√(aQ)·√(bQ) = √(ab)·Q` for nonnegative `a, b, Q`. -/
lemma sqrt_mul_sqrt_mul {a b Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 ≤ Q) :
    Real.sqrt (a * Q) * Real.sqrt (b * Q) = Real.sqrt (a * b) * Q := by
  have hsq : Real.sqrt Q * Real.sqrt Q = Q := by
    nlinarith [Real.sq_sqrt hQ]
  calc Real.sqrt (a * Q) * Real.sqrt (b * Q)
      = (Real.sqrt a * Real.sqrt b) * (Real.sqrt Q * Real.sqrt Q) := by
        rw [Real.sqrt_mul ha Q, Real.sqrt_mul hb Q]; ring
    _ = (Real.sqrt a * Real.sqrt b) * Q := by rw [hsq]
    _ = Real.sqrt (a * b) * Q := by rw [Real.sqrt_mul ha b]

/-- The conclusion of `Work.BoseFixB1S.corrChiScaleL2`. -/
def ChiL2 : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ∀ w : E3 → ℝ, Continuous w →
    (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ *
        (∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2)

/-- The conclusion of `Work.BoseFixB1S.corrPlanchMarg`. -/
def PlanchMarg : Prop :=
  ∀ ℓ d : ℝ, 0 < ℓ → 0 < d → ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
    MeasureTheory.Integrable (fun u : E3 =>
      ∫ z : E3, (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2) →
    (∫ u : E3, ∫ z : E3, (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2)
      = ∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2 →
    MeasureTheory.Integrable (fun u : E3 =>
        ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
          Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
      ∧ (∫ u : E3, ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
            Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)

/-- The conclusion of `Work.BoseFixB1S.corrArith`. -/
def Arith : Prop :=
  ∀ C₀ C₁ Cχ A : ℝ, 0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ Cχ → 0 < A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * A ^ 3 ≤ ε₀ →
      (let ℓ : ℝ := Work.BoseBox.sideAt μ A
       let d : ℝ := (Work.BoseBox.paramsAt μ A).d
       let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
       ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        ≤ Work.BoseBox.bValue / (4 * ℓ ^ 2))

/-! ### 6.1  The abbreviations of the correction step -/

/-- The `u`-windowed mean-free state `χ_{B(u)}·(w − c)` at FS's parameters. -/
def corrSt (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → E3 → ℝ :=
  fun u z => Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * (w z - c)

/-- The sliding-box mean `|B(u)|⁻¹∫_{B(u)}w` at FS's parameters. -/
def corrBC (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) : ℝ :=
  (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
    ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z'

/-- The flat mean `ℓ⁻³∫_{acube ℓ}w` at FS's parameters. -/
def corrMean (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : ℝ :=
  (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
    ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), w z

/-- The flat mean-square `Q` of the correction step. -/
def corrQ (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : ℝ :=
  ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
    (w z - corrMean v μ w) ^ 2

/-- The sliding-mean form on the left of the correction inequality. -/
def corrA (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : E3 → ℝ :=
  fun u => Work.BSKinetic.Decomp.bsW
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
    (corrSt v μ w (corrBC v μ w u) u)

/-- The flat-mean form on the right of the correction inequality. -/
def corrB (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => Work.BSKinetic.Decomp.bsW
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
    (corrSt v μ w c u)

/-- The squared sliding mean of `w − c`. -/
def corrBm (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => (corrBC v μ (fun z => w z - c) u) ^ 2

/-- The `L²`-norm of the `p`-transform of the mean-free state. -/
def corrH (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => Real.sqrt (∫ p : E3,
    ‖Work.BSKinetic.Decomp.bsPsi (corrSt v μ w c u) p‖ ^ 2)

/-- The cross term of the mean-shift expansion. -/
def corrX (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => |corrBC v μ (fun z => w z - c) u| * corrH v μ w c u

/-- The logarithmic factor `L = 1 + (ℓd)⁻¹ + |log d|` of `MeanSq`, at FS's parameters. -/
def corrL (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
    + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|

/-! ### 6.2  The unfolding equations of the abbreviations -/

lemma corrSt_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrSt v μ w c u = fun z => Submission.BoseGases.chiB
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * (w z - c) := rfl

lemma corrBC_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) :
    corrBC v μ w u = (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
      ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z' := rfl

lemma corrBm_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrBm v μ w c u = (corrBC v μ (fun z => w z - c) u) ^ 2 := rfl

lemma corrH_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrH v μ w c u = Real.sqrt (∫ p : E3,
      ‖Work.BSKinetic.Decomp.bsPsi (corrSt v μ w c u) p‖ ^ 2) := rfl

lemma corrX_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrX v μ w c u = |corrBC v μ (fun z => w z - c) u| * corrH v μ w c u := rfl

lemma corrA_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) :
    corrA v μ w u = Work.BSKinetic.Decomp.bsW
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
      (corrSt v μ w (corrBC v μ w u) u) := rfl

lemma corrB_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrB v μ w c u = Work.BSKinetic.Decomp.bsW
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
      (corrSt v μ w c u) := rfl

lemma corrQ_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) :
    corrQ v μ w = ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (w z - corrMean v μ w) ^ 2 := rfl

/-! ### 6.2  The assembly -/

/-- **The assembly**: the six pieces imply the target.  From `crux_pt` one derives
`∫_u (A_u − B_u) ≤ Kq∫_u bm² + 2√Kq ∫_u |bm|·H` by `integral_mono`,
then the `u`-Cauchy–Schwarz, Plancherel + the window partition and the arithmetic. -/
theorem cruxCorrB1_of_pieces {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hCut : CutWords v) (hMean : MeanSq v) (hMarg : Marginal v)
    (hArith : Arith) (hChi : ChiL2) (hPlanch : PlanchMarg) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g →
      ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ u : E3, Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (g z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, g z')))
        ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ u : E3, Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
              (fun z : E3 =>
                Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z')))
          + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
              (∫ z in Submission.BoseGases.acube
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z') ^ 2) := by
  obtain ⟨C₀, hC₀nn, ε_c, hεc, hcut⟩ := hCut
  obtain ⟨ε_m, hεm, C₁, hC₁nn, hmean⟩ := hMean
  obtain ⟨ε_g, hεg, hmarg⟩ := hMarg
  by_cases hav : 0 < _root_.BoseGases.a v
  · obtain ⟨ε_a, hεa, harith⟩ := hArith C₀ C₁ (Submission.BoseGases.chiNormSq)⁻¹
      (_root_.BoseGases.a v) hC₀nn hC₁nn
      (inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos)) hav
    refine ⟨min (min ε_c (min ε_m ε_g)) ε_a,
      lt_min (lt_min hεc (lt_min hεm hεg)) hεa, ?_⟩
    intro μ hμ g hg
    have hεcm : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_c :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hεmm : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_m :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεgm : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_g :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hεam : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_a := min_le_right _ _
    have hμc : Work.BoseBoxFix.Adm v ε_c μ := Work.BoseFixB1.Adm.mono hμ hεcm
    have hμm : Work.BoseBoxFix.Adm v ε_m μ := Work.BoseFixB1.Adm.mono hμ hεmm
    have hμg : Work.BoseBoxFix.Adm v ε_g μ := Work.BoseFixB1.Adm.mono hμ hεgm
    have hμ0 : 0 < μ := Work.BoseFixB1.adm_mu_pos hμ
    have hℓp : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
    have hdp : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hμ
    have hμd : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε_a :=
      le_trans (Work.BoseFixB1.adm_dilute hμ) hεam
    have hLnn : 0 ≤ corrL v μ := by
      rw [corrL]
      have h1 : 0 < ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ :=
        inv_pos.mpr (mul_pos hℓp hdp)
      have h2 : 0 ≤ |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)| :=
        abs_nonneg _
      linarith
    have hCχnn : 0 ≤ (Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos)
    have hQnn : 0 ≤ corrQ v μ g := integral_nonneg fun z => sq_nonneg _
    have hsubd : ContDiff ℝ (⊤ : ENat) (fun z : E3 => g z - corrMean v μ g) :=
      hg.sub contDiff_const
    have hsubc : Continuous (fun z : E3 => g z - corrMean v μ g) := hsubd.continuous
    have hAint : MeasureTheory.Integrable (corrA v μ g) := (hmarg μ hμg g hg).2.1
    have hBint : MeasureTheory.Integrable (corrB v μ g (corrMean v μ g)) :=
      (hmarg μ hμg (fun z : E3 => g z - corrMean v μ g) hsubd).1
    obtain ⟨hBmint, hBmbound⟩ := hmean μ hμm (fun z : E3 => g z - corrMean v μ g) hsubd
    have hPlan := hPlanch (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d hℓp hdp
      (fun z : E3 => g z - corrMean v μ g) hsubd
      (hmarg μ hμg (fun z : E3 => g z - corrMean v μ g) hsubd).2.2.1
      (hmarg μ hμg (fun z : E3 => g z - corrMean v μ g) hsubd).2.2.2
    have hH2int : MeasureTheory.Integrable
        (fun u : E3 => (corrH v μ g (corrMean v μ g) u) ^ 2) := by
      refine hPlan.1.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [corrH_eq]
      exact (Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)).symm
    have hH2val : ∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2
        = (2 * Real.pi) ^ 3 *
          (∫ z : E3, (Submission.BoseGases.chiScale
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
            * (g z - corrMean v μ g) ^ 2) := by
      calc ∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2
          = ∫ u : E3, ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
            simp only [corrH_eq]
            exact Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)
        _ = (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
              * (g z - corrMean v μ g) ^ 2) := hPlan.2
    have hH2bound : ∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2
        ≤ (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * corrQ v μ g := by
      rw [hH2val]
      have hchi := hChi (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hℓp
        (fun z : E3 => g z - corrMean v μ g) hsubc
      calc (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
              * (g z - corrMean v μ g) ^ 2)
          ≤ (2 * Real.pi) ^ 3 * ((Submission.BoseGases.chiNormSq)⁻¹ *
              (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - corrMean v μ g) ^ 2)) :=
            mul_le_mul_of_nonneg_left hchi (by positivity)
        _ = (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * corrQ v μ g := by
            simp only [corrQ_eq]
            ring
    have hAbsBm : AEStronglyMeasurable
        (fun u : E3 => |corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|) := by
      have h1 : AEStronglyMeasurable
          (fun u : E3 => Real.sqrt (corrBm v μ g (corrMean v μ g) u)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hBmint.aestronglyMeasurable
      refine h1.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [corrBm_eq]
      exact Real.sqrt_sq_eq_abs _
    have hHaes : AEStronglyMeasurable (corrH v μ g (corrMean v μ g)) := by
      have h1 : AEStronglyMeasurable
          (fun u : E3 => Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
            (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hPlan.1.aestronglyMeasurable
      exact h1
    have hBm_memLp : MeasureTheory.MemLp
        (fun u : E3 => |corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|) 2 := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq hAbsBm).mpr ?_
      refine hBmint.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [corrBm_eq]
      exact (sq_abs _).symm
    have hH_memLp : MeasureTheory.MemLp (corrH v μ g (corrMean v μ g)) 2 :=
      (MeasureTheory.memLp_two_iff_integrable_sq hHaes).mpr hH2int
    have hXcs : ∫ u : E3, corrX v μ g (corrMean v μ g) u
        ≤ Real.sqrt (C₁ * (corrL v μ) ^ 3
              * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹ * corrQ v μ g)
          * Real.sqrt ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * corrQ v μ g) := by
      have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hBm_memLp hH_memLp
      have h1 : ∫ u : E3, corrX v μ g (corrMean v μ g) u
          ≤ Real.sqrt (∫ u : E3, (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|) ^ 2)
            * Real.sqrt (∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2) :=
        le_trans (le_abs_self _) hcs
      refine le_trans h1 (mul_le_mul ?_ (Real.sqrt_le_sqrt hH2bound)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      refine Real.sqrt_le_sqrt (le_trans ?_ hBmbound)
      exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun u => by
        simp only [corrBm_eq]
        exact sq_abs _))
    have hpt : ∀ u : E3, corrA v μ g u
        ≤ corrB v μ g (corrMean v μ g) u
          + (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
              * corrBm v μ g (corrMean v μ g) u
          + 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
              * corrX v μ g (corrMean v μ g) u := by
      intro u
      obtain ⟨hInt_u, hQ_u, hE_u⟩ := hcut μ hμc u
      have hKqnn : 0 ≤ C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2 :=
        mul_nonneg hC₀nn (sq_nonneg _)
      have hcrux := crux_pt (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (κ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
        hℓp hdp hg u hKqnn hQ_u hE_u hInt_u (corrMean v μ g)
      have hring : 2 * (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u| *
            Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2) *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2))
          = 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2) *
            (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u| *
              Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
                (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2)) := by ring
      simp only [corrA_eq, corrB_eq, corrBm_eq, corrX_eq, corrH_eq, corrSt_eq, corrBC_eq]
        at hcrux hring ⊢
      linarith only [hcrux, hring]
    have hXint : MeasureTheory.Integrable (corrX v μ g (corrMean v μ g)) := by
      have hdom : MeasureTheory.Integrable (fun u : E3 =>
          (corrBm v μ g (corrMean v μ g) u + (corrH v μ g (corrMean v μ g) u) ^ 2) / 2) :=
        (hBmint.add hH2int).div_const 2
      refine hdom.mono' (hAbsBm.mul hHaes) ?_
      refine Filter.Eventually.of_forall fun u => ?_
      simp only [Real.norm_eq_abs, corrX_eq]
      have hb : 0 ≤ |corrBC v μ (fun z : E3 => g z - corrMean v μ g) u| := abs_nonneg _
      have hh : 0 ≤ corrH v μ g (corrMean v μ g) u := Real.sqrt_nonneg _
      simp only [abs_of_nonneg (mul_nonneg hb hh), corrBm_eq]
      nlinarith [sq_nonneg (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|
          - corrH v μ g (corrMean v μ g) u),
        sq_abs (corrBC v μ (fun z : E3 => g z - corrMean v μ g) u)]
    have hXint' : MeasureTheory.Integrable
        (fun u : E3 => 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
          * corrX v μ g (corrMean v μ g) u) :=
      hXint.const_mul _
    have hBmint' : MeasureTheory.Integrable
        (fun u : E3 => (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
          * corrBm v μ g (corrMean v μ g) u) :=
      hBmint.const_mul _
    have hsumint : MeasureTheory.Integrable
        (fun u : E3 => (corrB v μ g (corrMean v μ g) u
            + (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
                * corrBm v μ g (corrMean v μ g) u)
          + 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
              * corrX v μ g (corrMean v μ g) u) :=
      (hBint.add hBmint').add hXint'
    let Kq : ℝ := C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2
    let sB : ℝ := (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
    let A₁ : ℝ := Kq * C₁ * (corrL v μ) ^ 3 * sB
    let B₁ : ℝ := 2 * Real.sqrt Kq
      * Real.sqrt (C₁ * (corrL v μ) ^ 3 * sB * (2 * Real.pi) ^ 3
          * (Submission.BoseGases.chiNormSq)⁻¹)
    have hA₁ : A₁ = Kq * C₁ * (corrL v μ) ^ 3 * sB := rfl
    have hB₁ : B₁ = 2 * Real.sqrt Kq
        * Real.sqrt (C₁ * (corrL v μ) ^ 3 * sB * (2 * Real.pi) ^ 3
            * (Submission.BoseGases.chiNormSq)⁻¹) := rfl
    have hKqnn : 0 ≤ Kq := mul_nonneg hC₀nn (sq_nonneg _)
    have hsBnn : 0 ≤ sB := inv_nonneg.mpr (pow_nonneg (mul_pos hℓp hdp).le 3)
    have hcanon : ((2 * Real.pi) ^ 3)⁻¹ * (A₁ + B₁)
        ≤ Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) :=
      harith μ hμ0 hμd
    have hchain : ∫ u : E3, corrA v μ g u
        ≤ (∫ u : E3, corrB v μ g (corrMean v μ g) u)
          + (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
              + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)) := by
      have hI1 : ∫ u : E3, ((fun u : E3 => corrB v μ g (corrMean v μ g) u)
            + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u)) u
          = (∫ u : E3, corrB v μ g (corrMean v μ g) u)
            + (∫ u : E3, (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u) u) :=
        MeasureTheory.integral_add hBint hBmint'
      have hI2 : (∫ u : E3, (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u) u)
          = Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u) :=
        MeasureTheory.integral_const_mul _ _
      have hI3 : ∫ u : E3, (((fun u : E3 => corrB v μ g (corrMean v μ g) u)
            + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u))
            + (fun u : E3 => 2 * Real.sqrt Kq * corrX v μ g (corrMean v μ g) u)) u
          = (∫ u : E3, ((fun u : E3 => corrB v μ g (corrMean v μ g) u)
                + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u)) u)
            + (∫ u : E3, (fun u : E3 => 2 * Real.sqrt Kq
                * corrX v μ g (corrMean v μ g) u) u) :=
        MeasureTheory.integral_add (hBint.add hBmint') hXint'
      have hI4 : (∫ u : E3, (fun u : E3 => 2 * Real.sqrt Kq
              * corrX v μ g (corrMean v μ g) u) u)
          = 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u) :=
        MeasureTheory.integral_const_mul _ _
      have hmono := MeasureTheory.integral_mono hAint hsumint hpt
      calc ∫ u : E3, corrA v μ g u
          ≤ ∫ u : E3, (((fun u : E3 => corrB v μ g (corrMean v μ g) u)
                + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u))
              + (fun u : E3 => 2 * Real.sqrt Kq * corrX v μ g (corrMean v μ g) u)) u := hmono
        _ = (∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)) := by
            rw [hI3, hI1, hI2, hI4]; ring_nf
    have hA1 : Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u) ≤ A₁ * corrQ v μ g := by
      calc Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
          ≤ Kq * (C₁ * (corrL v μ) ^ 3 * sB * corrQ v μ g) :=
            mul_le_mul_of_nonneg_left hBmbound hKqnn
        _ = A₁ * corrQ v μ g := by rw [hA₁]; ring
    have hA2 : 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)
        ≤ B₁ * corrQ v μ g := by
      have hsq := sqrt_mul_sqrt_mul (a := C₁ * (corrL v μ) ^ 3 * sB)
        (b := (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹) (Q := corrQ v μ g)
        (mul_nonneg (mul_nonneg hC₁nn (pow_nonneg hLnn 3)) hsBnn)
        (mul_nonneg (by positivity) hCχnn) hQnn
      calc 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)
          ≤ 2 * Real.sqrt Kq * (Real.sqrt (C₁ * (corrL v μ) ^ 3 * sB * corrQ v μ g)
              * Real.sqrt ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹
                  * corrQ v μ g)) :=
            mul_le_mul_of_nonneg_left hXcs (by positivity)
        _ = B₁ * corrQ v μ g := by rw [hsq, hB₁]; ring
    have hcorr : Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
          + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)
        ≤ (A₁ + B₁) * corrQ v μ g := by
      calc _ ≤ A₁ * corrQ v μ g + B₁ * corrQ v μ g := add_le_add hA1 hA2
        _ = (A₁ + B₁) * corrQ v μ g := by rw [hA₁, hB₁]; ring
    have hfinal : ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, corrA v μ g u)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, corrB v μ g (corrMean v μ g) u)
          + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * corrQ v μ g := by
      have hpi : 0 < ((2 * Real.pi) ^ 3)⁻¹ := inv_pos.mpr (by positivity)
      have hY : ((2 * Real.pi) ^ 3)⁻¹ *
            (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
              + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u))
          ≤ (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * corrQ v μ g := by
        calc ((2 * Real.pi) ^ 3)⁻¹ *
              (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u))
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((A₁ + B₁) * corrQ v μ g) :=
              mul_le_mul_of_nonneg_left hcorr (le_of_lt hpi)
          _ = (((2 * Real.pi) ^ 3)⁻¹ * (A₁ + B₁)) * corrQ v μ g := by rw [hA₁, hB₁]; ring
          _ ≤ (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                * corrQ v μ g := mul_le_mul_of_nonneg_right hcanon hQnn
      calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, corrA v μ g u)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            ((∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u))) :=
            mul_le_mul_of_nonneg_left hchain (le_of_lt hpi)
        _ = ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + ((2 * Real.pi) ^ 3)⁻¹ *
                (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                  + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)) := by ring_nf
        _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                  * corrQ v μ g := add_le_add (le_refl _) hY
    exact hfinal
  · exact ⟨1, one_pos, fun μ hμ g hg => absurd (Work.BoseFixB1.adm_a_pos hμ) hav⟩


/-- **The `chiScale` `L²`-bound** (`ChiL2`): `chiScale ℓ` is supported in `acube ℓ` and its
square is bounded by `chiNormSq⁻¹`. -/
theorem chiL2 : ∀ ℓ : ℝ, 0 < ℓ → ∀ w : E3 → ℝ, Continuous w →
    (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ *
        (∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2) := by
  intro ℓ hℓ w hw
  have hcn : 0 < Submission.BoseGases.chiNormSq := Submission.BoseGases.chiNormSq_pos
  have hsup : Submission.BoseGases.chiSupAbs ^ 2 = (Submission.BoseGases.chiNormSq)⁻¹ := by
    rw [Submission.BoseGases.chiSupAbs, inv_pow, Real.sq_sqrt hcn.le]
  have hptsu : ∀ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ := by
    intro z
    rw [← hsup, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Submission.BoseGases.chiScale_abs_le_sup ℓ z) 2
  have hpt : ∀ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ *
          (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (w z) ^ 2) z := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]
      exact mul_le_mul_of_nonneg_right (hptsu z) (sq_nonneg _)
    · have h0 : Submission.BoseGases.chiScale ℓ z = 0 := by
        by_contra hc
        exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hc)
      rw [Set.indicator_of_notMem hz, h0]
      simp
  set ξ : E3 → ℝ := fun z : E3 => Submission.BoseGases.chiScale ℓ z * w z with hξdef
  have hξc : Continuous ξ := by
    rw [hξdef]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.mul hw
  have hξs : HasCompactSupport ξ := by
    rw [hξdef]
    exact (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
  have hLi : MeasureTheory.Integrable (fun z : E3 =>
      (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
    have h1 : MeasureTheory.Integrable (ξ * ξ) :=
      (hξc.mul hξc).integrable_of_hasCompactSupport (hξs.mul_right (f' := ξ))
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    show ξ z * ξ z = (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2
    rw [hξdef]
    ring
  have hRi : MeasureTheory.Integrable (fun z : E3 =>
      (Submission.BoseGases.chiNormSq)⁻¹ *
        (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (w z) ^ 2) z) := by
    have hcmp : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
    have hOn : MeasureTheory.IntegrableOn (fun z : E3 => (w z) ^ 2)
        (Submission.BoseGases.acube ℓ) :=
      ((hw.pow 2).continuousOn).integrableOn_compact (μ := MeasureTheory.volume) hcmp
    exact ((integrable_indicator_iff hcmp.measurableSet).mpr hOn).const_mul _
  calc (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      ≤ ∫ z : E3, (Submission.BoseGases.chiNormSq)⁻¹ *
          (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (w z) ^ 2) z :=
        MeasureTheory.integral_mono_ae hLi hRi (Filter.Eventually.of_forall hpt)
    _ = (Submission.BoseGases.chiNormSq)⁻¹ *
          (∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]

/-- **The arithmetic of the payment** (`Arith`): with `t = μ A³`, `ℓ = A t^{-163/323}`,
`d = t^{6/323}`, `L = 1 + (ℓd)⁻¹ + |log d|`, both summands of the payment are
`C t^{δ}(1+|log t|)^{3/2}` with `δ > 0` (`Work.BoseFixB1.RegimeAux`,
`Work.BoseFixB1S.fsXpLogSmall`), while the right-hand side `bValue/(4ℓ²) = (1/64)ℓ⁻²` is
comparatively large; the whole comparison is carried by the two auxiliary quantities
`Q = L³(ℓd)⁻³` and `R = ℓ²Q`, both `≤ K₀` for `t` below the threshold. -/
theorem arithKH : Arith := by
  intro C₀ C₁ Cχ A h₀ h₁ hχ hA
  have hAinvnn : 0 ≤ A⁻¹ := inv_nonneg.mpr hA.le
  have h1Ainvnn : 0 ≤ 1 + A⁻¹ := by linarith
  set c₂ : ℝ := (2 * Real.pi) ^ 3 with hc₂
  have hc₂pos : 0 < c₂ := by rw [hc₂]; positivity
  have hc₂le : c₂ ≤ 512 := by
    rw [hc₂]
    have h1 : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have h2 : 0 ≤ 2 * Real.pi := by positivity
    calc (2 * Real.pi) ^ 3 ≤ (8 : ℝ) ^ 3 := pow_le_pow_left₀ h2 h1 3
      _ = 512 := by norm_num
  have hC₀C₁ : 0 ≤ C₀ * C₁ := mul_nonneg h₀ h₁
  set S : ℝ := Real.sqrt C₀ * Real.sqrt (C₁ * c₂ * Cχ) with hS
  have hSnn : 0 ≤ S := by rw [hS]; positivity
  set D : ℝ := C₀ * C₁ + 2 * S + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hDC : C₀ * C₁ ≤ D := by rw [hD]; linarith
  have hDS : 2 * S ≤ D := by rw [hD]; linarith
  set K₀ : ℝ := (c₂ / (256 * D)) ^ 2 with hK₀
  have hK₀nn : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hsK₀ : Real.sqrt K₀ = c₂ / (256 * D) := by
    rw [hK₀, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hphi : C₀ * C₁ * K₀ + 2 * S * Real.sqrt K₀ ≤ c₂ / 64 := by
    rw [hsK₀]
    have h1 : C₀ * C₁ * K₀ ≤ c₂ / 128 := by
      have hKD : K₀ = c₂ ^ 2 / (256 ^ 2 * D ^ 2) := by
        rw [hK₀, div_pow, mul_pow]
      have hstep : D * (c₂ ^ 2 / (256 ^ 2 * D ^ 2)) = c₂ ^ 2 / (256 ^ 2 * D) := by
        field_simp
      calc C₀ * C₁ * K₀ ≤ D * K₀ := mul_le_mul_of_nonneg_right hDC hK₀nn
        _ = D * (c₂ ^ 2 / (256 ^ 2 * D ^ 2)) := by rw [hKD]
        _ = c₂ ^ 2 / (256 ^ 2 * D) := hstep
        _ ≤ c₂ ^ 2 / 256 ^ 2 := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [sq_nonneg c₂, hD1]
        _ ≤ c₂ / 128 := by
              rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 256 ^ 2)]
              nlinarith [hc₂pos, hc₂le]
    have h2 : 2 * S * (c₂ / (256 * D)) ≤ c₂ / 128 := by
      have hc₂nn : 0 ≤ c₂ := hc₂pos.le
      calc 2 * S * (c₂ / (256 * D)) = 2 * S * c₂ / (256 * D) := by ring
        _ ≤ D * c₂ / (256 * D) := by
              apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ 256 * D)
              exact mul_le_mul_of_nonneg_right hDS hc₂nn
        _ = c₂ / 256 := by field_simp
        _ ≤ c₂ / 128 := by
              rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
              nlinarith [hc₂pos]
    linarith [h1, h2]
  obtain ⟨ε₁, hε₁, hb₁⟩ := Work.BoseFixB1S.fsXpLogSmall (c := 471) (M := 3)
    (K := K₀ / ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3 + 1)) (by positivity) (by norm_num) (by norm_num)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Work.BoseFixB1S.fsXpLogSmall (c := 145) (M := 3)
    (K := K₀ / ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ + 1)) (by positivity) (by norm_num) (by norm_num)
  refine ⟨min ε₁ (min ε₂ 1), lt_min hε₁ (lt_min hε₂ one_pos), ?_⟩
  intro μ hμ hμle
  have ht : 0 < μ * A ^ 3 := by positivity
  have ht1 : μ * A ^ 3 ≤ 1 := le_trans hμle (le_trans (min_le_right _ _) (min_le_right _ _))
  have htε₁ : μ * A ^ 3 ≤ ε₁ := le_trans hμle (min_le_left _ _)
  have htε₂ : μ * A ^ 3 ≤ ε₂ := le_trans hμle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb₁'' : (1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) 471
      ≤ K₀ / ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3 + 1) := by
    rw [mul_comm]
    exact hb₁ _ ht htε₁
  have hb₂'' : (1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) 145
      ≤ K₀ / ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ + 1) := by
    rw [mul_comm]
    exact hb₂ _ ht htε₂
  dsimp only
  set ℓ : ℝ := Work.BoseBox.sideAt μ A with hℓdef
  set d : ℝ := (Work.BoseBox.paramsAt μ A).d with hddef
  set L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d| with hLdef
  have hcast3 : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  have hLconv : L ^ 3 = L ^ (3 : ℝ) := by rw [← Real.rpow_natCast L 3, hcast3]
  rw [hLconv]
  have hℓval : ℓ = A * Work.BoseBox.fsXp (μ * A ^ 3) (-163) := by
    rw [hℓdef]; exact Work.BoseFixB1.sideAt_eq_fsXp hA hμ
  have hdval : d = Work.BoseBox.fsXp (μ * A ^ 3) 6 := by
    rw [hddef]; exact Work.BoseFixB1.d_eq_fsXp μ A
  have hℓdval : ℓ * d = A * Work.BoseBox.fsXp (μ * A ^ 3) (-157) := by
    rw [hℓdef, hddef]
    exact (mul_comm (Work.BoseBox.sideAt μ A) (Work.BoseBox.paramsAt μ A).d).trans
      (Work.BoseFixB1.d_mul_sideAt_eq hA hμ)
  have hℓpos : 0 < ℓ := by rw [hℓval]; exact mul_pos hA (Work.BoseBox.fsXp_pos ht)
  have hdpos : 0 < d := by rw [hdval]; exact Work.BoseBox.fsXp_pos ht
  have hℓdpos : 0 < ℓ * d := mul_pos hℓpos hdpos
  have hfsinv : Work.BoseBox.fsXp (μ * A ^ 3) (-157)
      = (Work.BoseBox.fsXp (μ * A ^ 3) 157)⁻¹ := by
    rw [Work.BoseBox.fsXp_inv ht 157]
  have hXval : ((ℓ * d) ^ 3)⁻¹ = A⁻¹ ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) 471 := by
    rw [hℓdval, hfsinv, mul_pow, mul_inv]
    rw [← inv_pow, ← inv_pow, inv_inv]
    rw [Work.BoseBox.fsXp_pow (le_of_lt ht) 157 3]
    norm_num
  have hX2 : ℓ ^ 2 * ((ℓ * d) ^ 3)⁻¹ = A⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) 145 := by
    rw [hXval, hℓval, mul_pow]
    rw [Work.BoseBox.fsXp_pow (le_of_lt ht) (-163) 2]
    rw [show A ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) (-163 * ((2 : ℕ) : ℝ)) *
          (A⁻¹ ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) 471)
        = A ^ 2 * A⁻¹ ^ 3 *
            (Work.BoseBox.fsXp (μ * A ^ 3) (-163 * ((2 : ℕ) : ℝ)) *
              Work.BoseBox.fsXp (μ * A ^ 3) 471) by ring]
    rw [Work.BoseBox.fsXp_mul ht]
    have hexp : -163 * ((2 : ℕ) : ℝ) + 471 = (145 : ℝ) := by norm_num
    rw [hexp]
    have hA2 : A ^ 2 * A⁻¹ ^ 3 = A⁻¹ := by
      rw [inv_pow]
      field_simp
    rw [hA2]
  have hLinv : (ℓ * d)⁻¹ ≤ A⁻¹ := by
    rw [hℓdval, hfsinv, mul_inv, inv_inv]
    calc A⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) 157 ≤ A⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left
            (Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)) hAinvnn
      _ = A⁻¹ := mul_one _
  have hlogd : |Real.log d| = (6 / 323) * |Real.log (μ * A ^ 3)| := by
    rw [hdval]
    dsimp only [Work.BoseBox.fsXp]
    rw [Real.log_rpow ht, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6 / 323)]
  have hlogle : |Real.log d| ≤ |Real.log (μ * A ^ 3)| := by
    rw [hlogd]
    nlinarith [abs_nonneg (Real.log (μ * A ^ 3))]
  have hLle : L ≤ (1 + A⁻¹) * (1 + |Real.log (μ * A ^ 3)|) := by
    rw [hLdef]
    nlinarith [hLinv, hlogle, abs_nonneg (Real.log (μ * A ^ 3)), hAinvnn]
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    have h1 : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr hℓdpos.le
    have h2 : 0 ≤ |Real.log d| := abs_nonneg _
    linarith
  have hL3 : L ^ (3 : ℝ) ≤ (1 + A⁻¹) ^ (3 : ℝ) * (1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ) := by
    have h := Real.rpow_le_rpow hLnn hLle (by norm_num : (0 : ℝ) ≤ 3)
    rwa [Real.mul_rpow h1Ainvnn (by positivity : (0 : ℝ) ≤ 1 + |Real.log (μ * A ^ 3)|)] at h
  have hQle : L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹ ≤ K₀ := by
    have hcum : 0 ≤ A⁻¹ ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) 471 :=
      mul_nonneg (pow_nonneg hAinvnn 3) (Work.BoseBox.fsXp_nonneg ht.le)
    have hD₀ : 0 ≤ (1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3 :=
      mul_nonneg (Real.rpow_nonneg h1Ainvnn 3) (pow_nonneg hAinvnn 3)
    calc L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹
        = L ^ (3 : ℝ) * (A⁻¹ ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) 471) := by rw [hXval]
      _ ≤ ((1 + A⁻¹) ^ (3 : ℝ) * (1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ)) *
            (A⁻¹ ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) 471) :=
          mul_le_mul_of_nonneg_right hL3 hcum
      _ = ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3) *
            ((1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) 471) :=
          mul_mul_mul_comm _ _ _ _
      _ ≤ ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3) *
            (K₀ / ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3 + 1)) :=
          mul_le_mul_of_nonneg_left hb₁'' hD₀
      _ ≤ K₀ := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ ^ 3 + 1)]
          nlinarith [hK₀nn]
  have hRle : ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹) ≤ K₀ := by
    have hcum : 0 ≤ A⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) 145 :=
      mul_nonneg hAinvnn (Work.BoseBox.fsXp_nonneg ht.le)
    have hD₀ : 0 ≤ (1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ :=
      mul_nonneg (Real.rpow_nonneg h1Ainvnn 3) hAinvnn
    calc ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)
        = L ^ (3 : ℝ) * (ℓ ^ 2 * ((ℓ * d) ^ 3)⁻¹) := by ring
      _ = L ^ (3 : ℝ) * (A⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) 145) := by rw [hX2]
      _ ≤ ((1 + A⁻¹) ^ (3 : ℝ) * (1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ)) *
            (A⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) 145) := mul_le_mul_of_nonneg_right hL3 hcum
      _ = ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹) *
            ((1 + |Real.log (μ * A ^ 3)|) ^ (3 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) 145) :=
          mul_mul_mul_comm _ _ _ _
      _ ≤ ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹) *
            (K₀ / ((1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ + 1)) :=
          mul_le_mul_of_nonneg_left hb₂'' hD₀
      _ ≤ K₀ := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 + A⁻¹) ^ (3 : ℝ) * A⁻¹ + 1)]
          nlinarith [hK₀nn]
  have hs1 : Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) = Real.sqrt C₀ * ℓ⁻¹ := by
    rw [Real.sqrt_mul h₀]
    congr 1
    exact Real.sqrt_sq (inv_nonneg.mpr hℓpos.le)
  have hs2 : Real.sqrt (C₁ * L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹ * c₂ * Cχ)
      = Real.sqrt (C₁ * c₂ * Cχ) * Real.sqrt (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹) := by
    have harg : C₁ * L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹ * c₂ * Cχ
        = (C₁ * c₂ * Cχ) * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹) := by ring
    rw [harg, Real.sqrt_mul (by positivity)]
  have hR : ℓ * Real.sqrt (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)
      = Real.sqrt (ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)) := by
    rw [Real.sqrt_mul (sq_nonneg ℓ), Real.sqrt_sq hℓpos.le]
  have hbridge : c₂⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹
        + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹ * c₂ * Cχ))
      = c₂⁻¹ * (ℓ⁻¹) ^ 2 * (C₀ * C₁ * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)
          + 2 * S * Real.sqrt (ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹))) := by
    rw [hs1, hs2, hS, ← hR]
    field_simp
  rw [hbridge]
  have hphib : C₀ * C₁ * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)
      + 2 * S * Real.sqrt (ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)) ≤ c₂ / 64 := by
    have h1 : C₀ * C₁ * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹) ≤ C₀ * C₁ * K₀ :=
      mul_le_mul_of_nonneg_left hQle hC₀C₁
    have h2 : 2 * S * Real.sqrt (ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹))
        ≤ 2 * S * Real.sqrt K₀ :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRle) (by linarith : (0 : ℝ) ≤ 2 * S)
    linarith [hphi]
  have hfin : (1 / 64 : ℝ) * (ℓ⁻¹) ^ 2 = Work.BoseBox.bValue / (4 * ℓ ^ 2) := by
    rw [Work.BoseBox.bValue]
    field_simp
    norm_num
  calc c₂⁻¹ * (ℓ⁻¹) ^ 2 * (C₀ * C₁ * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)
        + 2 * S * Real.sqrt (ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)))
      = (ℓ⁻¹) ^ 2 * (c₂⁻¹ * (C₀ * C₁ * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)
        + 2 * S * Real.sqrt (ℓ ^ 2 * (L ^ (3 : ℝ) * ((ℓ * d) ^ 3)⁻¹)))) := by ring
    _ ≤ (ℓ⁻¹) ^ 2 * (c₂⁻¹ * (c₂ / 64)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hphib (inv_nonneg.mpr hc₂pos.le)
        · exact sq_nonneg _
    _ = (1 / 64 : ℝ) * (ℓ⁻¹) ^ 2 := by field_simp
    _ = Work.BoseBox.bValue / (4 * ℓ ^ 2) := hfin

/-- **The `u`-marginal bookkeeping** (`Marginal`): the four conjuncts of the `u`-marginal
statement at `v`, assembled from the `u`-support of `chiB`, the box-mean
measurability/boundedness and the Tonelli marginal of `chiB`. -/
theorem marginalKH {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Marginal v := by
  refine ⟨1, one_pos, fun μ hμ w hw => ?_⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hμ
  have hwc : Continuous w := hw.continuous
  obtain ⟨hMmeas, C₀, hC₀, hMbd⟩ :=
    Work.BoseFixB1S.corr.measurableBoxMeanKH
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd hwc
  obtain ⟨hint3, hid4⟩ :=
    Work.BoseFixB1S.integrable_and_marginal_chiB
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd hwc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := Work.BoseFixB1S.corr.integrableBSWCutKH
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd (g := w) hw
      (ρ := fun _ : E3 => 0) measurable_const ⟨0, fun u => by simp⟩
    simpa using h1
  · have h2 := Work.BoseFixB1S.corr.integrableBSWCutKH
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd (g := w) hw
      (ρ := fun u : E3 => (Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)⁻¹ *
        ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) hMmeas ⟨C₀, hMbd⟩
    simpa [one_div] using h2
  · exact hint3
  · exact hid4

/-- **The intersection-mean correction** — the residual `Work.BoseFixB1S.CorrInput v` expanded:
for every smooth `g` and every admissible `μ`,
`{
  (2π)⁻³ ∫_u bsW (fsKinCoeff c_sb) (χ_{B(u)}·(g − ⍍_{B(u)}g)) du
    ≤ (2π)⁻³ ∫_u bsW (fsKinCoeff c_sb) (χ_{B(u)}·(g − ⍍_{acube ℓ}g)) du
      + (bValue/(4·ℓ²)) · ∫_{acube ℓ} (g − ⍍_{acube ℓ}g)² }`
where `ℓ = sideAt μ (a v)`, `c_sb = sbCut μ (a v) = (d s ℓ)⁻¹`, `χ_{B(u)} = chiB ℓ P.d u`,
`B(u) = dlBox ℓ P.d u`, `⍍_{B(u)} = boxMass⁻¹∫_{dlBox}`, `⍍_{acube ℓ} = ℓ⁻³∫_{acube ℓ}`, and the
`∃ ε₀ > 0, ∀ μ, Adm v ε₀ μ →` packaging.  This is the `(E2)`+`(E3)` mean-mismatch step of
`FINDING_unprojected_route_B.md`: replacing the *intersection*-box mean `⍍_{B(u)}g` by the
*anchored* mean `⍍_{acube ℓ}g` inside the sliding window is paid by the flat anchored mass. -/
theorem corrInputB1KH {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    Work.BoseFixB1S.CorrInput v :=
  cruxCorrB1_of_pieces h (Work.BoseFixB1S.corrCutWordsSharp h)
    (Work.BoseFixB1S.corr.corrMeanSqKH h)
    (marginalKH h) arithKH chiL2
    (fun ℓ d hℓ hd w hw hint heq => Work.BoseFixB1S.corrPlanchMarg hℓ hd hw hint heq)

end Work.BoseFixB1.KH.corr
