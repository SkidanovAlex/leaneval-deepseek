import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.continuous_bsPsi
import Submission.Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixR.Kin.Expand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.MM.linearCombination` — the `bsW` algebra and the pointwise mean-shift step

Copied (with the namespace changed from `Work.BoseFixB1S` to `Work.BoseFixB1.Core.MM`, and with
no other edit) from the *proved* supporting lemmas of
`Submission/Work/BoseFixB1S/cruxCorrB1.lean` (Sections 1-3 and 5), which carries a `sorry` in its
final assembly and therefore cannot be imported by a `sorry`-free file.

* `bsPsi_const_mul`, `bsPsi_const_mul_normSq`, `bsW_const_mul`, `Fsq_bsPsi_const_mul`,
  `integrable_Fsq_bsPsi_const_mul`: scalar homogeneity of the `p`-transform and of `bsW`.
* `bsWBilin_le_sqrt`: the `L²`-Cauchy–Schwarz bound `|bsWBilin F a b| ≤ √(∫F²‖bsPsi b‖²)·√(∫‖bsPsi a‖²)`.
* `chiScale_sq_le`: `χ_ℓ(z)² ≤ chiNormSq⁻¹`.
* `integrable_fsKinCoeff_cross`: the pairing integrand of two smooth compactly supported states.
* `boxMean_sub_const`: the box mean of `g − c` is the box mean of `g` minus `c`.
* `crux_pt`: the pointwise mean-shift step — the expansion of `bsW F (χ(ψ − ⍍χψ))` at the sliding
  box mean as the anchored flat-mean value plus the box-mean square and the cross term.
-/

noncomputable section
open MeasureTheory
open scoped Real Topology BigOperators ContDiff ENNReal

namespace Work.BoseFixB1.Core.MM

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


end Work.BoseFixB1.Core.MM
