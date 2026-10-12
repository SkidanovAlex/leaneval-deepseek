import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Measure.Integral

open MeasureTheory

theorem integrable_norm_sq_div_one_add_pow (k : ℕ) (hk : 6 ≤ k) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 / (1 + ‖p‖) ^ k) := by
  -- The dominating function `(1 + ‖p‖)^{-4}` is integrable in dimension 3 since `4 > 3`.
  have hbase : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (1 + ‖p‖) ^ (-(4 : ℝ))) := by
    have h := integrable_one_add_norm (μ := volume) (E := EuclideanSpace ℝ (Fin 3))
      (r := (4 : ℝ)) ?_
    · simpa using h
    · have : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by
        rw [finrank_euclideanSpace_fin]; norm_num
      rw [this]; norm_num
  refine hbase.mono' ?_ ?_
  · exact (Measurable.div (measurable_norm.pow_const 2)
      ((measurable_const.add measurable_norm).pow_const k)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (by positivity)]
    -- write the natural power as a real power
    rw [← Real.rpow_natCast (1 + ‖p‖) k]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + ‖p‖) (k : ℝ))]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖p‖)]
    have h2 : ‖p‖ ^ 2 ≤ (1 + ‖p‖) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
      nlinarith
    have hexp : (2 : ℝ) ≤ -4 + (k : ℝ) := by
      have : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have h1 : (1 : ℝ) ≤ 1 + ‖p‖ := by have := norm_nonneg p; linarith
    have hrpow : (1 + ‖p‖) ^ (2 : ℝ) ≤ (1 + ‖p‖) ^ (-4 + (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le h1 hexp
    calc ‖p‖ ^ 2 ≤ (1 + ‖p‖) ^ 2 := h2
      _ = (1 + ‖p‖) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ ≤ (1 + ‖p‖) ^ (-4 + (k : ℝ)) := hrpow

end Commons.Measure.Integral