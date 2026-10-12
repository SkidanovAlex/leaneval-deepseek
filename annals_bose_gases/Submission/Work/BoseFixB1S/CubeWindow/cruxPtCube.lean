import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.cruxCorrB1
import Submission.Work.BoseFixB1S.kineticCruxParsed
import Submission.Work.BoseFixB1S.weightedPlancherelKinFT
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.CubeWindow.cruxPtCube`

The pointwise mean-shift step of the sliding spectral half at the **cube** cutoff
`χ = chiSmallB M ℓ d u` (a `C^{M-1}` window, `M ≥ 5`).

The proof re-runs the argument of `Work.BoseFixB1S.crux_pt` (and of the general-window
`Work.BoseFixB1B.crux_ptGen`), whose only hypotheses on the window are smoothness and compact
support, at the *weakened* regularity `C¹` that the cube cutoff actually has.  The `C¹`
substitutes of the `⊤`-regularity tools of that argument are proved in §1 below:

* `continuous_kinFT_weak`, `weakKinFTPlanch` — continuity and `L²`/second-moment integrability of
  the `p`-convention Fourier transform of a `C¹` compactly supported function (only
  `Work.BoseFixB1S.weightedPlancherelKinFT` is needed, which is stated at `ContDiff ℝ 1`);
* `integrable_phase_mul_weak`, `bsPsi_add_weak`, `bsW_add_weak` — additivity of `bsPsi` and the
  exact bilinear expansion of `bsW`;
* `integrable_fsKinCoeff_mul_bsPsi_sq_weak`, `integrable_fsKinCoeff_cross_weak` — the `p`-space
  integrabilities entering that expansion;
* `bilin_le_sqrt_weak` — Cauchy–Schwarz for the cross term.

The general statement is `cruxPtGenWeak`; `cruxPtCube` is its instantiation at
`Submission.BoseGases.chiSmallB M ℓ d u`, using `Work.BoseFixB1S.win.contDiff_chiSmallB` (`C¹`
from `2 ≤ M`), `Submission.BoseGases.chiSmallB_hasCompactSupport` and
`Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ContDiff ENNReal

namespace Work.BoseFixB1S.CubeWindow

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1.  The weakened-regularity analytic substitutes -/

/-- `kinFT F` is continuous for a continuous compactly supported `F`. -/
theorem continuous_kinFT_weak {F : E3 → ℂ} (hFc : Continuous F) (hFcs : HasCompactSupport F) :
    Continuous (fun p : E3 => Submission.BoseGases.kinFT F p) := by
  have hint : Integrable F := hFc.integrable_of_hasCompactSupport hFcs
  show Continuous (fun p : E3 =>
    ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y)
  refine continuous_of_dominated
    (F := fun (p y : E3) => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y)
    (bound := fun y : E3 => ‖F y‖) ?_ ?_ ?_ ?_
  · intro p
    exact (by fun_prop : Continuous fun y : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y).aestronglyMeasurable
  · intro p
    filter_upwards with y
    rw [norm_mul, Work.BSKinetic.Decomp.norm_exp_neg_I_inner p y, one_mul]
  · simpa using hint.norm
  · filter_upwards with y
    fun_prop

/-- The `C¹` Plancherel integrability: both the `L²` mass and the second moment of `kinFT F`. -/
theorem weakKinFTPlanch {F : E3 → ℂ} (hF1 : ContDiff ℝ 1 F) (hFcs : HasCompactSupport F) :
    MeasureTheory.Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      ∧ MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2) := by
  have hw := (Work.BoseFixB1S.weightedPlancherelKinFT hF1 hFcs).1
  have hcont : Continuous (fun p : E3 => Submission.BoseGases.kinFT F p) :=
    continuous_kinFT_weak hF1.continuous hFcs
  constructor
  · refine hw.mono' (hcont.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_left (sq_nonneg _) (by linarith [sq_nonneg ‖p‖])
  · refine hw.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((continuous_norm.pow 2).mul (hcont.norm.pow 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (by linarith [sq_nonneg ‖p‖]) (sq_nonneg _)

/-- The phase-multiplied integrand of a continuous compactly supported state is integrable. -/
lemma integrable_phase_mul_weak {h : E3 → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h)
    (p : E3) :
    Integrable (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (h z : ℂ)) := by
  have h1 : Integrable (fun z : E3 => (h z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) :=
    ((Complex.continuous_ofReal.comp hc).integrable_of_hasCompactSupport
      (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))).mul_bdd (by fun_prop)
      (Filter.Eventually.of_forall (fun z =>
        le_of_eq (Work.BSKinetic.Decomp.norm_exp_neg_I_inner p z)))
  exact h1.congr (Filter.Eventually.of_forall (fun z => mul_comm _ _))

/-- Additivity of `bsPsi` at `C¹`. -/
lemma bsPsi_add_weak {a b : E3 → ℝ} (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 1 b) (hbc : HasCompactSupport b) (p : E3) :
    Work.BSKinetic.Decomp.bsPsi (fun z => a z + b z) p
      = Work.BSKinetic.Decomp.bsPsi a p + Work.BSKinetic.Decomp.bsPsi b p := by
  have h1 : Integrable (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((a z : ℝ) : ℂ)) :=
    integrable_phase_mul_weak ha.continuous hac p
  have h2 : Integrable (fun z : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((b z : ℝ) : ℂ)) :=
    integrable_phase_mul_weak hb.continuous hbc p
  rw [Work.BSKinetic.Decomp.bsPsi, Work.BSKinetic.Decomp.bsPsi, Work.BSKinetic.Decomp.bsPsi,
    Submission.BoseGases.kinFT, Submission.BoseGases.kinFT, Submission.BoseGases.kinFT]
  have hpt : ∀ z : E3,
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((a z + b z : ℝ) : ℂ))
        = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((a z : ℝ) : ℂ)
          + Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((b z : ℝ) : ℂ) := by
    intro z; push_cast; ring
  rw [show (∫ z : E3,
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((a z + b z : ℝ) : ℂ)))
      = ∫ z : E3, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((a z : ℝ) : ℂ)
          + Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((b z : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add h1 h2]

/-- Continuity of `bsPsi` at `C⁰`. -/
theorem continuous_bsPsi_weak {h : E3 → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi h p) := by
  have h1 : Continuous (fun z : E3 => (h z : ℂ)) := Complex.continuous_ofReal.comp hc
  have h2 : HasCompactSupport (fun z : E3 => (h z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  simpa only [Work.BSKinetic.Decomp.bsPsi] using continuous_kinFT_weak h1 h2

/-- The exact bilinear expansion of `bsW` at `C¹`. -/
theorem bsW_add_weak {F : ℝ → ℝ} {a b : E3 → ℝ}
    (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 1 b) (hbc : HasCompactSupport b)
    (hia : MeasureTheory.Integrable (fun p : E3 =>
      F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2))
    (hib : MeasureTheory.Integrable (fun p : E3 =>
      F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2))
    (hii : MeasureTheory.Integrable (fun p : E3 =>
      F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
        star (Work.BSKinetic.Decomp.bsPsi b p)).re)) :
    Work.BSKinetic.Decomp.bsW F (fun z => a z + b z)
      = Work.BSKinetic.Decomp.bsW F a + 2 * Work.BoseFixR.bsWBilin F a b
        + Work.BSKinetic.Decomp.bsW F b := by
  have hpt : ∀ p : E3, F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi (fun z => a z + b z) p‖ ^ 2
      = F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
        + 2 * (F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re)
        + F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2 := by
    intro p
    rw [bsPsi_add_weak ha hac hb hbc p, Work.BoseFixR.normSq_add_pointwise]
    ring
  have hcongr : (∫ p : E3, F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi (fun z => a z + b z) p‖ ^ 2)
      = ∫ p : E3, (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
          + 2 * (F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
              star (Work.BSKinetic.Decomp.bsPsi b p)).re)
          + F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hsplit : (∫ p : E3, (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
        + 2 * (F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re)
        + F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2))
      = (∫ p : E3, F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2)
        + 2 * (∫ p : E3, F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re)
        + ∫ p : E3, F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2 := by
    have h1 : Integrable (fun p : E3 => F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
        + 2 * (F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re)) := hia.add (hii.const_mul 2)
    rw [show (∫ p : E3, (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
          + 2 * (F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
              star (Work.BSKinetic.Decomp.bsPsi b p)).re)
          + F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2))
        = ∫ p : E3, (fun q : E3 => F ‖q‖ * ‖Work.BSKinetic.Decomp.bsPsi a q‖ ^ 2
              + 2 * (F ‖q‖ * (Work.BSKinetic.Decomp.bsPsi a q *
                  star (Work.BSKinetic.Decomp.bsPsi b q)).re)) p
            + (fun q : E3 => F ‖q‖ * ‖Work.BSKinetic.Decomp.bsPsi b q‖ ^ 2) p from rfl]
    rw [integral_add h1 hib]
    congr 1
    rw [show (∫ p : E3, (fun q : E3 => F ‖q‖ * ‖Work.BSKinetic.Decomp.bsPsi a q‖ ^ 2
              + 2 * (F ‖q‖ * (Work.BSKinetic.Decomp.bsPsi a q *
                  star (Work.BSKinetic.Decomp.bsPsi b q)).re)) p)
        = ∫ p : E3, (fun q : E3 => F ‖q‖ * ‖Work.BSKinetic.Decomp.bsPsi a q‖ ^ 2) p
            + (fun q : E3 => 2 * (F ‖q‖ * (Work.BSKinetic.Decomp.bsPsi a q *
                star (Work.BSKinetic.Decomp.bsPsi b q)).re)) p from rfl]
    rw [integral_add hia (hii.const_mul 2), integral_const_mul]
  rw [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsW,
    Work.BoseFixR.bsWBilin, hcongr, hsplit]

/-- The `fsKinCoeff`-weighted diagonal mass is integrable at `C¹`. -/
theorem integrable_fsKinCoeff_mul_bsPsi_sq_weak {c : ℝ} {h : E3 → ℝ}
    (hd : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    MeasureTheory.Integrable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
  have hFc : ContDiff ℝ 1 (fun z : E3 => (h z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hd
  have hFcs : HasCompactSupport (fun z : E3 => (h z : ℂ)) :=
    hc.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hpl := weakKinFTPlanch hFc hFcs
  have hKint : MeasureTheory.Integrable (fun p : E3 =>
      ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
    simpa only [Work.BSKinetic.Decomp.bsPsi] using hpl.1
  have hK2int : MeasureTheory.Integrable (fun p : E3 =>
      ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
    simpa only [Work.BSKinetic.Decomp.bsPsi] using hpl.2
  have hGint : MeasureTheory.Integrable (fun p : E3 =>
      (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
    have h1 : MeasureTheory.Integrable (fun p : E3 =>
        2 * (‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)) := hK2int.const_mul 2
    have h2 : MeasureTheory.Integrable (fun p : E3 =>
        (2 * c ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := hKint.const_mul (2 * c ^ 2)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    ring
  have hcont : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) :=
    ((continuous_norm.sub continuous_const).max continuous_const).pow 2
  have haesm : AEStronglyMeasurable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) :=
    hcont.aestronglyMeasurable.mul hKint.aestronglyMeasurable
  refine hGint.mono' haesm (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c ‖p‖)
    (sq_nonneg _)

/-- Cauchy–Schwarz for `bsWBilin` at `C¹`. -/
lemma bilin_le_sqrt_weak {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (hFc : Continuous F) {a b : E3 → ℝ}
    (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 1 b) (hbc : HasCompactSupport b)
    (hFb : MeasureTheory.Integrable (fun p : E3 =>
      F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2)) :
    |Work.BoseFixR.bsWBilin F a b|
      ≤ Real.sqrt (∫ p : E3, F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2)
        * Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2) := by
  have hconta : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi a p) :=
    continuous_bsPsi_weak ha.continuous hac
  have hcontb : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi b p) :=
    continuous_bsPsi_weak hb.continuous hbc
  have hbmeas : AEStronglyMeasurable (fun p : E3 =>
      F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) :=
    (((hFc.comp continuous_norm).mul hcontb.norm)).aestronglyMeasurable
  have hameas : AEStronglyMeasurable (fun p : E3 => ‖Work.BSKinetic.Decomp.bsPsi a p‖) :=
    hconta.norm.aestronglyMeasurable
  have hbsq : MeasureTheory.Integrable
      (fun p : E3 => (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) ^ 2) := by
    refine hFb.congr (Filter.Eventually.of_forall fun p => ?_)
    change F ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2
      = (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) ^ 2
    ring
  have hasq : MeasureTheory.Integrable (fun p : E3 =>
      ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2) := by
    have hFcC : ContDiff ℝ 1 (fun z : E3 => (a z : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ha
    have hFcsC : HasCompactSupport (fun z : E3 => (a z : ℂ)) :=
      hac.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
    simpa only [Work.BSKinetic.Decomp.bsPsi] using (weakKinFTPlanch hFcC hFcsC).1
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
      F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
        star (Work.BSKinetic.Decomp.bsPsi b p)).re) := by
    refine hprod_int.mono' ?_ ?_
    · exact (((hFc.comp continuous_norm).mul hcont_re)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF ‖p‖), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hF ‖p‖)
      calc |(Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re|
          ≤ ‖Work.BSKinetic.Decomp.bsPsi a p *
              star (Work.BSKinetic.Decomp.bsPsi b p)‖ := Complex.abs_re_le_norm _
        _ = ‖Work.BSKinetic.Decomp.bsPsi b p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ := by
            rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj, mul_comm]
  have hmain : |Work.BoseFixR.bsWBilin F a b| ≤ ∫ p : E3,
      (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) * ‖Work.BSKinetic.Decomp.bsPsi a p‖ := by
    rw [Work.BoseFixR.bsWBilin]
    have h2 : ‖(∫ p : E3,
          F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re : ℝ)‖
        ≤ ∫ p : E3, ‖(F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re : ℝ)‖ :=
      MeasureTheory.norm_integral_le_integral_norm (μ := volume)
        (f := fun p : E3 => F ‖p‖ * (Work.BSKinetic.Decomp.bsPsi a p *
          star (Work.BSKinetic.Decomp.bsPsi b p)).re)
    simp only [Real.norm_eq_abs] at h2
    refine le_trans h2 ?_
    refine MeasureTheory.integral_mono hbd_int.abs hprod_int (fun p => ?_)
    rw [abs_mul, abs_of_nonneg (hF ‖p‖), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hF ‖p‖)
    calc |(Work.BSKinetic.Decomp.bsPsi a p *
          star (Work.BSKinetic.Decomp.bsPsi b p)).re|
        ≤ ‖Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)‖ := Complex.abs_re_le_norm _
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
  rw [show (fun p : E3 => (F ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖) *
        ‖Work.BSKinetic.Decomp.bsPsi a p‖)
      = fun p : E3 =>
          (fun q : E3 => F ‖q‖ * ‖Work.BSKinetic.Decomp.bsPsi b q‖) p *
          (fun q : E3 => ‖Work.BSKinetic.Decomp.bsPsi a q‖) p from rfl]
  exact hcs

/-- The `fsKinCoeff`-weighted cross integrand is integrable at `C¹`. -/
theorem integrable_fsKinCoeff_cross_weak {c : ℝ} {a b : E3 → ℝ}
    (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 1 b) (hbc : HasCompactSupport b) :
    MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (Work.BSKinetic.Decomp.bsPsi a p * star (Work.BSKinetic.Decomp.bsPsi b p)).re) := by
  have hFc : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
    simp only [Submission.BoseGases.fsKinCoeff]; fun_prop
  have hca : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi a p) :=
    continuous_bsPsi_weak ha.continuous hac
  have hcb : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi b p) :=
    continuous_bsPsi_weak hb.continuous hbc
  have hinta := integrable_fsKinCoeff_mul_bsPsi_sq_weak (c := c) ha hac
  have hintb := integrable_fsKinCoeff_mul_bsPsi_sq_weak (c := c) hb hbc
  have hdom : MeasureTheory.Integrable (fun p : E3 =>
      (Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
        + Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2) :=
    (hinta.add hintb).div_const 2
  refine hdom.mono' ?_ ?_
  · exact ((hFc.comp continuous_norm).mul
      (Complex.continuous_re.comp (hca.mul (continuous_star.comp hcb)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    have hFnn : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
    have ham : |(Work.BSKinetic.Decomp.bsPsi a p *
          star (Work.BSKinetic.Decomp.bsPsi b p)).re|
        ≤ ‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ := by
      calc |(Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re|
          ≤ ‖Work.BSKinetic.Decomp.bsPsi a p *
              star (Work.BSKinetic.Decomp.bsPsi b p)‖ := Complex.abs_re_le_norm _
        _ = ‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖ := by
            rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hFnn]
    have hgm : ‖Work.BSKinetic.Decomp.bsPsi a p‖ * ‖Work.BSKinetic.Decomp.bsPsi b p‖
        ≤ (‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
            + ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖Work.BSKinetic.Decomp.bsPsi a p‖
        - ‖Work.BSKinetic.Decomp.bsPsi b p‖)]
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          |(Work.BSKinetic.Decomp.bsPsi a p *
            star (Work.BSKinetic.Decomp.bsPsi b p)).re|
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
            (‖Work.BSKinetic.Decomp.bsPsi a p‖
              * ‖Work.BSKinetic.Decomp.bsPsi b p‖) :=
          mul_le_mul_of_nonneg_left ham hFnn
      _ ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
              + ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hgm hFnn
      _ = (Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi a p‖ ^ 2
            + Submission.BoseGases.fsKinCoeff c ‖p‖
              * ‖Work.BSKinetic.Decomp.bsPsi b p‖ ^ 2) / 2 := by ring

/-! ## 2.  The general weakened-regularity pointwise mean shift -/

/-- The pointwise mean-shift step for a `C¹` compactly supported window `χ` (this is
`Work.BoseFixB1B.crux_ptGen` with the regularity of the window and of the state relaxed to `C¹`,
which is what the cube cutoff `chiSmallB M ℓ d u` satisfies). -/
theorem cruxPtGenWeak {ℓ d κ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) {χ : E3 → ℝ}
    (hχd : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχ0 : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Submission.BoseGases.dlBox ℓ d u) = 0 → χ = 0)
    {g : E3 → ℝ} (hg : ContDiff ℝ 1 g) {Kq Ke : ℝ} (hKq : 0 ≤ Kq)
    (hQ : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ ≤ Kq)
    (hE : (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
        ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2) ≤ Ke)
    (hEint : MeasureTheory.Integrable (fun p : E3 =>
        (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
        ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2))
    (c0 : ℝ) :
    Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z : E3 => χ z *
          (g z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            (∫ z' in Submission.BoseGases.dlBox ℓ d u, g z')))
      ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
          (fun z : E3 => χ z * (g z - c0))
        + Kq * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            (∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0))) ^ 2
        + 2 * (|(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
                (∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0))| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : E3 => χ z * (g z - c0)) p‖ ^ 2)) := by
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set J : ℝ := ∫ z' in Submission.BoseGases.dlBox ℓ d u, g z' with hJdef
  set Jt : ℝ := ∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0) with hJtdef
  set bc : ℝ := (1 / V) * J with hbcdef
  set bm : ℝ := (1 / V) * Jt with hbmdef
  have hgtd : ContDiff ℝ 1 (fun z : E3 => g z - c0) := hg.sub contDiff_const
  have hFnn : ∀ r : ℝ, 0 ≤ Submission.BoseGases.fsKinCoeff κ r :=
    fun r => Submission.BoseGases.fsKinCoeff_nonneg κ r
  have hFcont : Continuous (Submission.BoseGases.fsKinCoeff κ) := by
    unfold Submission.BoseGases.fsKinCoeff; fun_prop
  by_cases hV0 : V = 0
  · -- the window vanishes on a null box
    have hχz : χ = 0 := hχ0 (by
      have hlt := Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
      rw [hVdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def] at hV0
      rcases (ENNReal.toReal_eq_zero_iff _).mp hV0 with h' | h'
      · exact h'
      · exact absurd h' hlt.ne)
    have hst : (fun z : E3 => χ z * (g z - bc)) = fun z : E3 => χ z * (g z - c0) := by
      funext z; rw [hχz]; simp
    have hsq0 : (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => χ z * (g z - c0)) p‖ ^ 2) = 0 := by
      have hz : (fun z : E3 => χ z * (g z - c0)) = fun _ : E3 => (0 : ℝ) := by
        funext z; rw [hχz]; simp
      rw [hz]
      simp [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]
    have hbm0 : bm = 0 := by rw [hbmdef, hV0, div_zero, zero_mul]
    rw [hst, hbm0, hsq0, Real.sqrt_zero]
    linarith [le_refl (Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
      (fun z : E3 => χ z * (g z - c0)))]
  · -- the genuine case
    have hVbox : Work.SmallBoxSliding.boxMass ℓ d u ≠ 0 := by rwa [hVdef] at hV0
    have hbmbc : bm = bc - c0 := by
      rw [hbmdef, hbcdef, hJtdef, hJdef, hVdef]
      exact Work.BoseFixB1S.boxMean_sub_const hℓ hd hg.continuous hVbox
    have hstate : (fun z : E3 => χ z * (g z - bc)) =
        fun z : E3 => χ z * (g z - c0) + (-(bc - c0)) * χ z := by
      funext z; ring
    have hξd : ContDiff ℝ 1 (fun z : E3 => χ z * (g z - c0)) := hχd.mul hgtd
    have hξc : HasCompactSupport (fun z : E3 => χ z * (g z - c0)) := hχc.mul_right
    have hbd : ContDiff ℝ 1 (fun z : E3 => (-(bc - c0)) * χ z) :=
      contDiff_const.mul hχd
    have hbcsh : HasCompactSupport (fun z : E3 => (-(bc - c0)) * χ z) :=
      HasCompactSupport.mul_left hχc
    have hi1 : MeasureTheory.Integrable (fun p : E3 =>
        Submission.BoseGases.fsKinCoeff κ ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => χ z * (g z - c0)) p‖ ^ 2) :=
      integrable_fsKinCoeff_mul_bsPsi_sq_weak hξd hξc
    have hi2 : MeasureTheory.Integrable (fun p : E3 =>
        Submission.BoseGases.fsKinCoeff κ ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => (-(bc - c0)) * χ z) p‖ ^ 2) :=
      integrable_fsKinCoeff_mul_bsPsi_sq_weak hbd hbcsh
    have hi3 : MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff κ ‖p‖ *
        (Work.BSKinetic.Decomp.bsPsi (fun z : E3 => χ z * (g z - c0)) p *
          star (Work.BSKinetic.Decomp.bsPsi (fun z : E3 => (-(bc - c0)) * χ z) p)).re) :=
      integrable_fsKinCoeff_cross_weak hξd hξc hbd hbcsh
    have hexp := bsW_add_weak (F := Submission.BoseGases.fsKinCoeff κ)
      hξd hξc hbd hbcsh hi1 hi2 hi3
    have hself : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z : E3 => (-(bc - c0)) * χ z)
        = (bc - c0) ^ 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ := by
      rw [Work.BoseFixB1S.bsW_const_mul]; ring
    have hFb : MeasureTheory.Integrable (fun p : E3 =>
        (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => (-(bc - c0)) * χ z) p‖ ^ 2) :=
      Work.BoseFixB1S.integrable_Fsq_bsPsi_const_mul (-(bc - c0)) hEint
    have hbound : |Work.BoseFixR.bsWBilin (Submission.BoseGases.fsKinCoeff κ)
          (fun z : E3 => χ z * (g z - c0)) (fun z : E3 => (-(bc - c0)) * χ z)|
        ≤ |bc - c0| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : E3 => χ z * (g z - c0)) p‖ ^ 2) := by
      have hble := bilin_le_sqrt_weak (F := Submission.BoseGases.fsKinCoeff κ) hFnn hFcont
        hξd hξc hbd hbcsh hFb
      have hFbval : (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => (-(bc - c0)) * χ z) p‖ ^ 2)
          = (bc - c0) ^ 2 * (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
              ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2) := by
        rw [Work.BoseFixB1S.Fsq_bsPsi_const_mul (F := Submission.BoseGases.fsKinCoeff κ)
          (w := χ) (-(bc - c0)), neg_sq]
      rw [hFbval] at hble
      have h1 : Real.sqrt ((bc - c0) ^ 2 * (∫ p : E3,
            (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi χ p‖ ^ 2)) ≤ |bc - c0| * Real.sqrt Ke := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (abs_nonneg _)
      exact le_trans hble (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _))
    have hQ' : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ ≤ Kq := hQ
    have hKq2 : (bc - c0) ^ 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ) χ
        ≤ Kq * (bc - c0) ^ 2 := by
      rw [mul_comm Kq]
      exact mul_le_mul_of_nonneg_left hQ' (sq_nonneg _)
    have hcr2 : 2 * Work.BoseFixR.bsWBilin (Submission.BoseGases.fsKinCoeff κ)
          (fun z : E3 => χ z * (g z - c0)) (fun z : E3 => (-(bc - c0)) * χ z)
        ≤ 2 * (|bc - c0| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : E3 => χ z * (g z - c0)) p‖ ^ 2)) := by
      have h1 : Work.BoseFixR.bsWBilin (Submission.BoseGases.fsKinCoeff κ)
          (fun z : E3 => χ z * (g z - c0)) (fun z : E3 => (-(bc - c0)) * χ z)
          ≤ |bc - c0| * Real.sqrt Ke *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : E3 => χ z * (g z - c0)) p‖ ^ 2) := le_trans (le_abs_self _) hbound
      linarith only [h1]
    rw [hstate, hexp, hself]
    have hbm' : (bc - c0) = bm := hbmbc.symm
    rw [hbm'] at hKq2 hcr2 ⊢
    linarith [hKq2, hcr2]

/-! ## 3.  The cube cutoff -/

/-- **The pointwise mean-shift step at the cube cutoff** (regularity `5 ≤ M`, so the window is `C^4`):
the sliding-window state with the *intersection-box* mean is dominated by the flat-mean state, plus
the box-mean square (paid by the cut word `Kq`) and the bilinear cross term (paid by the
`fsKinCoeff²`-weighted cut word `Ke` and the L²-mass of the flat-mean state).  Cube twin of
`Work.BoseFixB1.KH.corr.crux_pt`; the weakened-regularity substitutes for `bsW_add`,
`bsPsi_add`, `bsWBilin_le_sqrt` and `integrable_fsKinCoeff_mul_bsPsi_sq` are available at `C¹`
from `Work.BoseFixB1S.weightedPlancherelKinFT` (the window and all its products with smooth `g`
are `C^{M-1} ≥ C^4` and compactly supported). -/
theorem cruxPtCube {ℓ d κ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 5 ≤ M)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (u : EuclideanSpace ℝ (Fin 3)) {Kq Ke : ℝ} (hKq : 0 ≤ Kq)
    (hQ : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u z) ≤ Kq)
    (hE : (∫ p : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2) ≤ Ke)
    (hEint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2))
    (c0 : ℝ) :
    Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u z *
          (g z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            (∫ z' in Submission.BoseGases.dlBox ℓ d u, g z')))
      ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u z * (g z - c0))
        + Kq * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            (∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0))) ^ 2
        + 2 * (|(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
                (∫ z' in Submission.BoseGases.dlBox ℓ d u, (g z' - c0))| * Real.sqrt Ke *
            Real.sqrt (∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BSKinetic.Decomp.bsPsi
              (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB M ℓ d u z * (g z - c0)) p‖ ^ 2)) := by
  refine cruxPtGenWeak (ℓ := ℓ) (d := d) (κ := κ) hℓ hd u
    (Work.BoseFixB1S.win.contDiff_chiSmallB 1 M (by omega) (ne_of_gt hℓ) (ne_of_gt hd) u)
    (Submission.BoseGases.chiSmallB_hasCompactSupport (by omega) hℓ u)
    (fun h0 => Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero (by omega) hℓ hd u h0)
    (hg.of_le (by simp)) hKq hQ hE hEint c0

end Work.BoseFixB1S.CubeWindow
