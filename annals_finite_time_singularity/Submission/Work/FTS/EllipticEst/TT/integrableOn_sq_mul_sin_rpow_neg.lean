import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set Filter
open scoped Real Topology

/-- Pointwise domination of `(f θ)^2 * (sin (2θ))^{-q}` on the open interval `(0, π/2)`.

Since `sin (2θ) ∈ (0,1]` there and `q ≤ 2`, the bound `|f θ| ≤ K sin (2θ)` gives
`|f θ|^2 * (sin (2θ))^{-q} ≤ K^2 * (sin (2θ))^{2-q} ≤ K^2`. -/
private lemma abs_sq_mul_sin_rpow_neg_le {f : ℝ → ℝ} {q K : ℝ} (hq2 : q ≤ 2)
    (hbd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ K * Real.sin (2 * θ)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖(f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)‖ ≤ K ^ 2 := by
  intro θ hθ
  have hθ1 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  set s := Real.sin (2 * θ) with hs_def
  have hs_pos : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs_le1 : s ≤ 1 := by rw [hs_def]; exact Real.sin_le_one _
  have hf2 : (f θ) ^ 2 ≤ (K * s) ^ 2 := by
    have h := hbd θ hθ
    rw [← hs_def] at h
    calc (f θ) ^ 2 = |f θ| ^ 2 := by rw [sq_abs]
      _ ≤ (K * s) ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) h
  have hs2 : s ^ 2 * s ^ (-q) ≤ 1 := by
    have h1 : s ^ 2 * s ^ (-q) = s ^ (2 - q) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs_pos]
      congr 1
    rw [h1]
    exact Real.rpow_le_one (le_of_lt hs_pos) hs_le1 (by linarith)
  have hsq : (0 : ℝ) ≤ s ^ (-q) := Real.rpow_nonneg (le_of_lt hs_pos) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsq)]
  calc (f θ) ^ 2 * s ^ (-q)
      ≤ (K * s) ^ 2 * s ^ (-q) := mul_le_mul_of_nonneg_right hf2 hsq
    _ = K ^ 2 * (s ^ 2 * s ^ (-q)) := by rw [mul_pow]; ring
    _ ≤ K ^ 2 * 1 := mul_le_mul_of_nonneg_left hs2 (sq_nonneg K)
    _ = K ^ 2 := by ring

theorem integrableOn_sq_mul_sin_rpow_neg {f : ℝ → ℝ} {q K : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (hK : 0 ≤ K) (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ K * Real.sin (2 * θ)) :
    MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
  -- The integrand is continuous on the open interval `(0, π/2)`.
  have hcont : ContinuousOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (Set.Ioo 0 (Real.pi / 2)) := by
    apply ContinuousOn.mul
    · exact hf.pow 2
    · apply ContinuousOn.rpow_const
      · fun_prop
      · intro θ hθ
        left
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hfinite : MeasureTheory.volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  -- Integrability on the open interval, from the uniform bound.
  have hIntIoo : MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) (Set.Ioo 0 (Real.pi / 2)) := by
    refine IntegrableOn.of_bound hfinite (hcont.aestronglyMeasurable measurableSet_Ioo) (K ^ 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact abs_sq_mul_sin_rpow_neg_le hq2 hbd θ hθ
  -- The two endpoints have measure zero, so the closed interval is equivalent.
  have hmeq : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  rw [Work.Spaces.Iθ]
  change MeasureTheory.Integrable (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
  rw [hmeq]
  exact hIntIoo

end Work.FTS.EllipticEst.TT
