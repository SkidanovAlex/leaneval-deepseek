import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
import Submission.Work.OneBodyKin.integrable_chiMul_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- `(1 + ‖p‖)^{-10} = ((1+‖p‖)^10)^{-1}` is integrable on `ℝ³` (`10 > 3 = finrank`). -/
private lemma integrable_one_add_norm_neg_ten :
    MeasureTheory.Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 10)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 10) (by
    rw [finrank_euclideanSpace]; norm_num)
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖) ^ (-(10 : ℝ)) = ((1 + ‖p‖ : ℝ) ^ 10)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  congr 1
  exact Real.rpow_natCast (1 + ‖p‖) 10

/-- **Pointwise domination.**  If `|profHat p| ≤ C/(1+‖p‖)^6`, then for every `n ≤ 2` the weighted
square `profHat(p)² ‖p‖^n` is dominated by the integrable profile `C² (1+‖p‖)^{-10}`. -/
private lemma profHat_sq_mul_norm_pow_le {C : ℝ}
    (hd : ∀ p : ℝ³, |profHat p| ≤ C / (1 + ‖p‖) ^ 6)
    {n : ℕ} (hn : n ≤ 2) (p : ℝ³) :
    (profHat p) ^ 2 * ‖p‖ ^ n ≤ C ^ 2 * ((1 + ‖p‖ : ℝ) ^ 10)⁻¹ := by
  have hr : (0 : ℝ) < 1 + ‖p‖ := by positivity
  -- `‖p‖^n ≤ (1+‖p‖)^2`
  have hn_le : ‖p‖ ^ n ≤ (1 + ‖p‖) ^ 2 := by
    calc ‖p‖ ^ n ≤ (1 + ‖p‖) ^ n :=
          pow_le_pow_left₀ (norm_nonneg p) (by linarith [norm_nonneg p]) n
      _ ≤ (1 + ‖p‖) ^ 2 := pow_le_pow_right₀ (by linarith [norm_nonneg p]) hn
  -- `profHat(p)^2 ≤ C^2/(1+‖p‖)^12`
  have hprof : (profHat p) ^ 2 ≤ C ^ 2 / (1 + ‖p‖) ^ 12 := by
    have h1 : (profHat p) ^ 2 ≤ (C / (1 + ‖p‖) ^ 6) ^ 2 := by
      rw [← sq_abs (profHat p)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hd p) 2
    rw [div_pow, ← pow_mul] at h1
    norm_num at h1
    exact h1
  calc (profHat p) ^ 2 * ‖p‖ ^ n
      ≤ (C ^ 2 / (1 + ‖p‖) ^ 12) * (1 + ‖p‖) ^ 2 :=
        mul_le_mul hprof hn_le (pow_nonneg (norm_nonneg p) n)
          (div_nonneg (sq_nonneg C) (by positivity))
    _ = C ^ 2 * ((1 + ‖p‖ : ℝ) ^ 10)⁻¹ := by
        rw [div_mul_eq_mul_div, div_eq_mul_inv]
        field_simp

theorem integrable_profHat_sq_mul_norm_pow (n : ℕ) (hn : n ≤ 2) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ n) := by
  obtain ⟨C, _hC, hd⟩ := ProfHatDecay
  refine (integrable_one_add_norm_neg_ten.const_mul (C ^ 2)).mono' ?_ ?_
  · exact ((continuous_profHat.pow 2).mul (continuous_norm.pow n)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) n))]
    exact profHat_sq_mul_norm_pow_le hd hn p

end Work.OneBodyKin
