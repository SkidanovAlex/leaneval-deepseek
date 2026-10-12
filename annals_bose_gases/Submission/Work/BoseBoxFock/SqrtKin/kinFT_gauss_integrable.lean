import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_decay_gen
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `p ↦ e^{−t‖p‖²}·kinFT g p` for smooth compactly supported `g`

`Submission.BoseGases.kinFT g` is the `p`-convention Fourier transform of `g`; for `g` smooth
with compact support it decays faster than any power of `‖p‖`
(`Work.BoseBoxFock.SqrtKin.kinFT_decay_gen`), while the Gaussian factor
`Real.exp (−(t‖p‖²))` is bounded by `1` for `t > 0`.  Hence the product is dominated by
`K (1 + ‖p‖)^{-4}`, which is integrable on `ℝ³` since `4 > 3 = finrank ℝ ℝ³`
(Mathlib's `integrable_one_add_norm`).  Continuity of `kinFT g`
(`Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable`) supplies measurability.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.SqrtKin

/-- The domination profile `K (1 + ‖p‖)^{-4}` is integrable on `ℝ³`. -/
private lemma integrable_one_add_norm_inv_four :
    Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 4)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 4) (by
    rw [finrank_euclideanSpace_fin]; norm_num)
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖ : ℝ) ^ 4)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  congr 1
  exact Real.rpow_natCast (1 + ‖p‖) 4

theorem kinFT_gauss_integrable {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ) * Submission.BoseGases.kinFT g p) := by
  -- `g` is integrable, hence `kinFT g` is continuous
  have hgint : Integrable g volume :=
    hg.continuous.integrable_of_hasCompactSupport (μ := volume) hgc
  have hcont : Continuous (Submission.BoseGases.kinFT g) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hgint
  -- quartic decay of `kinFT g`
  obtain ⟨K, _hK, hdec⟩ := kinFT_decay_gen hg hgc 4
  have hdom : Integrable (fun p : ℝ³ => K * ((1 + ‖p‖ : ℝ) ^ 4)⁻¹) :=
    integrable_one_add_norm_inv_four.const_mul K
  refine hdom.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_norm.pow 2)).neg))).mul hcont).aestronglyMeasurable
  · filter_upwards with p
    have hexp : Real.exp (-(t * ‖p‖ ^ 2)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht.le (sq_nonneg ‖p‖)))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖
        ≤ 1 * (K / (1 + ‖p‖) ^ 4) :=
          mul_le_mul hexp (hdec p) (norm_nonneg _) (by norm_num)
      _ = K * ((1 + ‖p‖ : ℝ) ^ 4)⁻¹ := by rw [one_mul, div_eq_mul_inv]

end Work.BoseBoxFock.SqrtKin
