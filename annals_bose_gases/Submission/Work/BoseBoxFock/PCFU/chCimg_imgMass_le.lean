import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseBoxFock.lintegral_periodisation_boxL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chCimg_imgMass_le` — the lattice-image mass of the low cut-off kernel

The position-space kernel `Κ_κ(z) = lowKer fc κ z = (2π)⁻³∫_p f(‖p‖/κ)cos⟪p,z⟫` of FS's
low-momentum multiplier is periodised by the lattice `ℓℤ³`.  This module proves that the mass of
the *nonzero* image sum, integrated over the centred box `acube ℓ`, is bounded by a **fixed**
constant (namely `1`) times the total mass `∫_z |Κ_κ(z)| dz`, uniformly in `ℓ`, `κ`, and the
translation `w`:

    ∫_{u ∈ acube ℓ} ‖Σ'_{d ≠ 0} Κ_κ(u + w + ℓ • latVec d)‖ du ≤ ∫_z |Κ_κ(z)| dz .

## The proof

The point is that the **translated boxes tile `ℝ³`**, so *no decay of the kernel is needed*.
Write `T u` for the complex image sum and `G u = ‖T u‖`.  Then

* `‖Σ'_d c_d‖ₑ ≤ Σ'_d ‖c_d‖ₑ` (`enorm_tsum_le_tsum_enorm`) and each summand of the (`d ≠ 0`)
  image sum is dominated by `‖Κ_κ(u + w + ℓ•latVec d)‖ₑ`, so
  `‖G u‖ₑ ≤ Σ'_d ‖Κ_κ(u + w + ℓ•latVec d)‖ₑ` pointwise;
* `ENNReal.ofReal (∫ G) ≤ ‖∫ T‖ₑ ≤ ∫⁻ ‖G‖ₑ` (via `enorm_integral_le_lintegral_enorm`, which in
  this Mathlib carries no measurability hypothesis, and `Real.enorm_eq_ofReal_abs`);
* `∫⁻_{acube ℓ} Σ'_d ‖Κ_κ(u + w + ℓ•latVec d)‖ₑ = ∫⁻_z ‖Κ_κ z‖ₑ` — this is the **tiling /
  periodisation identity**, obtained from `Work.BoseBoxFock.lintegral_periodisation_boxL`
  (applied to `z ↦ Κ_κ(z + w)` and combined with the translation invariance
  `lintegral_add_right_eq_self` and `boxL_eq_acube`), with no summation interchange;
* finally `∫⁻_z ‖Κ_κ z‖ₑ = ENNReal.ofReal (∫_z |Κ_κ z|)` by
  `ofReal_integral_norm_eq_lintegral_enorm` for the integrable `Κ_κ`.

The integrability of `Κ_κ` is the standard `(1+‖z‖)^{-4}` decay estimate (`lowKer_decay`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The low-momentum kernel is integrable.**  `lowKer_decay` at `N = 2` bounds it by
`C₀ (1+‖z‖)^{-4}`, which is integrable on `ℝ³`. -/
private lemma integrable_lowKer_imgMass (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun z : E3 => Work.BoseBoxFock.PCFU.lowKer fc κ z) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := Work.BoseBoxFock.PCFU.lowKer_decay fc hκ 2
  have hdec : ∀ z : E3, ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖
      ≤ C₀ * (1 + ‖z‖) ^ (-((4 : ℕ) : ℤ)) := by
    intro z
    have hz := hC₀ z
    have hpos : (0 : ℝ) < (1 + ‖z‖) ^ 4 := by positivity
    calc ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖
        = ((1 + ‖z‖) ^ 4)⁻¹
            * ((1 + ‖z‖) ^ 4 * ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ ((1 + ‖z‖) ^ 4)⁻¹ * C₀ := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hpos.le)
      _ = C₀ * (1 + ‖z‖) ^ (-((4 : ℕ) : ℤ)) := by rw [zpow_neg, zpow_natCast]; ring
  have hone : Integrable (fun z : E3 => (1 + ‖z‖) ^ (-((4 : ℕ) : ℤ))) := by
    have h1 : Integrable (fun z : E3 => (1 + ‖z‖) ^ (-((4 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
    refine h1.congr ?_
    filter_upwards with z
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, zpow_neg, zpow_natCast]
  exact (hone.const_mul C₀).mono'
    ((Work.BoseBoxFock.PCFU.lowKer_regular fc hκ).1.aestronglyMeasurable)
    (Filter.Eventually.of_forall hdec)

/-- **The lattice image sum of `‖lowKer‖` has total mass `∫⁻ ‖lowKer‖ₑ`.**  This is the tiling
identity: the translates `acube ℓ + ℓ•latVec d` cover `ℝ³` (`Work.BoseBoxFock.boxL_eq_acube` with
`Work.BoseBoxFock.lintegral_periodisation_boxL`), with the kernel translated by `w`. -/
private lemma lintegral_imgSum_lowKer (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (w : E3) :
    (∫⁻ u in Submission.BoseGases.acube ℓ,
        ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
          (u + w + ℓ • Work.BoseBoxFock.latVec d)‖ₑ)
      = ∫⁻ z : E3, ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖ₑ := by
  have hmeas : AEMeasurable (fun z : E3 => Work.BoseBoxFock.PCFU.lowKer fc κ (z + w)) volume :=
    ((Work.BoseBoxFock.PCFU.lowKer_regular fc hκ).1.comp (by fun_prop)).aemeasurable
  have hper := Work.BoseBoxFock.lintegral_periodisation_boxL hℓ hmeas
  have htrans : (∫⁻ z : E3, ‖Work.BoseBoxFock.PCFU.lowKer fc κ (z + w)‖ₑ)
      = ∫⁻ z : E3, ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖ₑ :=
    MeasureTheory.lintegral_add_right_eq_self
      (fun z : E3 => ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖ₑ) w
  rw [show (∫⁻ u in Submission.BoseGases.acube ℓ,
        ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
          (u + w + ℓ • Work.BoseBoxFock.latVec d)‖ₑ)
      = ∫⁻ u in Submission.BoseGases.acube ℓ,
        ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
          (u + ℓ • Work.BoseBoxFock.latVec d + w)‖ₑ from
    lintegral_congr fun u => tsum_congr fun d =>
      congrArg (fun t => ‖Work.BoseBoxFock.PCFU.lowKer fc κ t‖ₑ) (by abel)]
  rw [show (∫⁻ u in Submission.BoseGases.acube ℓ,
        ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
          (u + ℓ • Work.BoseBoxFock.latVec d + w)‖ₑ)
      = ∫⁻ z in Work.BoseK15.corpusBox.boxL ℓ,
        ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
          (z + ℓ • Work.BoseBoxFock.latVec d + w)‖ₑ from by
    rw [Work.BoseBoxFock.boxL_eq_acube hℓ]]
  rw [hper, htrans]

theorem chCimg_imgMass_le (fc : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ {κ : ℝ}, 0 < κ →
      ∀ w : EuclideanSpace ℝ (Fin 3),
      (∫ u in Submission.BoseGases.acube ℓ,
          ‖∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ) else
            ((Work.BoseBoxFock.PCFU.lowKer fc κ
              (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖)
        ≤ C * (∫ z : EuclideanSpace ℝ (Fin 3), |Work.BoseBoxFock.PCFU.lowKer fc κ z|) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro ℓ hℓ κ hκ w
  have hIntK : Integrable (fun z : E3 => Work.BoseBoxFock.PCFU.lowKer fc κ z) :=
    integrable_lowKer_imgMass fc hκ
  -- the integrand `F u = ‖T u‖`
  set F : E3 → ℝ := fun u => ‖∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ) else
      ((Work.BoseBoxFock.PCFU.lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
    with hF
  -- the pointwise domination of the image sum by the (unsigned) lattice sum of `‖lowKer‖`
  have hpt : ∀ u : E3, ‖F u‖ₑ
      ≤ ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
          (u + w + ℓ • Work.BoseBoxFock.latVec d)‖ₑ := by
    intro u
    rw [hF]
    rw [enorm_norm]
    exact (enorm_tsum_le_tsum_enorm).trans (ENNReal.tsum_le_tsum fun d => by
      split
      · simp
      · rw [enorm_le_iff_norm_le]; simp)
  -- the Bochner integral of `F` is dominated by the `lintegral` of `‖F‖ₑ`
  have hstep1 : ENNReal.ofReal (∫ u in Submission.BoseGases.acube ℓ, F u)
      ≤ ∫⁻ u in Submission.BoseGases.acube ℓ, ‖F u‖ₑ := by
    have h := enorm_integral_le_lintegral_enorm
      (μ := volume.restrict (Submission.BoseGases.acube ℓ)) F
    rw [Real.enorm_eq_ofReal_abs] at h
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans h
  have htil := lintegral_imgSum_lowKer fc hκ hℓ w
  have hfin : (∫⁻ z : E3, ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖ₑ)
      = ENNReal.ofReal (∫ z : E3, |Work.BoseBoxFock.PCFU.lowKer fc κ z|) := by
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hIntK]
    exact congrArg ENNReal.ofReal (integral_congr_ae
      (Filter.Eventually.of_forall fun z => Real.norm_eq_abs _))
  have hchain : ENNReal.ofReal (∫ u in Submission.BoseGases.acube ℓ, F u)
      ≤ ∫⁻ z : E3, ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖ₑ :=
    hstep1.trans ((lintegral_mono hpt).trans (le_of_eq htil))
  have hrhs_nn : 0 ≤ (∫ z : E3, |Work.BoseBoxFock.PCFU.lowKer fc κ z|) :=
    integral_nonneg fun z => abs_nonneg _
  have hmain : (∫ u in Submission.BoseGases.acube ℓ, F u)
      ≤ ∫ z : E3, |Work.BoseBoxFock.PCFU.lowKer fc κ z| :=
    (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp (hchain.trans hfin.le)
  simpa using hmain

end Work.BoseBoxFock.PCFU
