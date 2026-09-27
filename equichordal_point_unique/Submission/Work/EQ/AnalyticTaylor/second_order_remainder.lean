import Mathlib

open Metric Set Asymptotics Filter

namespace Work.EQ.AnalyticTaylor

/-- Second-order Taylor remainder estimate for a holomorphic function bounded by `M` on the
open disk of radius `R` about the origin, with `f 0 = 0`.

This is the quantitative form of the Schwarz lemma at order two: from `‖f‖ ≤ M` on the
disk of radius `R` and `f 0 = 0` one gets `‖deriv f 0‖ ≤ M / R` (Cauchy / Schwarz estimate),
and then the generalized Schwarz lemma applied to `w ↦ f w - deriv f 0 * w` gives the
`(‖v‖ / R)^2` decay of the residual, with constant `2`. -/
theorem second_order_remainder {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (h0 : f 0 = 0)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∀ v : ℂ, v ∈ Metric.ball (0 : ℂ) R → ‖f v - deriv f 0 * v‖ ≤ 2 * M * (‖v‖ / R) ^ 2 := by
  intro v hv
  -- `f` maps the open disk to the closed disk of radius `M` about `f 0 = 0`.
  have hMaps : Set.MapsTo f (Metric.ball (0 : ℂ) R) (Metric.closedBall (f 0) M) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, h0, sub_zero]
    exact hM z hz
  -- Cauchy / Schwarz estimate on the derivative at the center.
  have hderiv : ‖deriv f 0‖ ≤ M / R :=
    Complex.norm_deriv_le_div_of_mapsTo_ball hd hMaps hR
  -- The residual function `F w = f w - deriv f 0 * w`.
  set F : ℂ → ℂ := fun w => f w - deriv f 0 * w with hF
  have hF0 : F 0 = 0 := by simp [hF, h0]
  have hdF : DifferentiableOn ℂ F (Metric.ball 0 R) := by
    rw [hF]; exact hd.sub (by fun_prop)
  -- `F` maps the disk of radius `R` into the closed disk of radius `M + ‖deriv f 0‖ * R`.
  have hmapsF : Set.MapsTo F (Metric.ball (0 : ℂ) R)
      (Metric.closedBall (F 0) (M + ‖deriv f 0‖ * R)) := by
    intro w hw
    have hwlt : ‖w‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hw
    rw [Metric.mem_closedBall, dist_eq_norm, hF0, sub_zero]
    rw [hF]
    simp only []
    calc ‖f w - deriv f 0 * w‖ ≤ ‖f w‖ + ‖deriv f 0 * w‖ := norm_sub_le _ _
      _ = ‖f w‖ + ‖deriv f 0‖ * ‖w‖ := by rw [norm_mul]
      _ ≤ M + ‖deriv f 0‖ * R := by
            apply add_le_add
            · exact hM w (by rwa [Metric.mem_ball, dist_zero_right])
            · exact mul_le_mul_of_nonneg_left (le_of_lt hwlt) (norm_nonneg _)
  -- `F w = o(‖w‖)` at `0`, since `f` is differentiable at `0` with derivative `deriv f 0`.
  have hlittle : (fun w => F w - F 0) =o[nhds (0 : ℂ)] (fun w => ‖w - 0‖ ^ (1 : ℕ)) := by
    have hf' : HasDerivAt f (deriv f 0) 0 :=
      (hd.differentiableAt (Metric.ball_mem_nhds 0 hR)).hasDerivAt
    have h1 : (fun w => F w - F 0) =o[nhds (0 : ℂ)] (fun w => w - 0) := by
      have h := hf'.isLittleO
      have hfun : (fun x' => f x' - f 0 - (x' - 0) • deriv f 0) = (fun w => F w - F 0) := by
        funext w; simp only [hF, h0, smul_eq_mul, sub_zero]; ring
      rwa [hfun] at h
    have h2 : (fun w : ℂ => w - 0) =O[nhds (0 : ℂ)] (fun w => ‖w - 0‖ ^ (1 : ℕ)) := by
      have hh := (isBigO_norm_right (f := fun w : ℂ => w - 0) (g' := fun w : ℂ => w - 0)
          (l := nhds (0 : ℂ))).mpr (isBigO_refl _ _)
      simpa using hh
    exact h1.trans_isBigO h2
  -- Generalized Schwarz lemma at order two (n = 1).
  have hmain := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (f := F) (c := (0 : ℂ)) (z := v) (R₁ := R) (R₂ := M + ‖deriv f 0‖ * R) (n := 1)
      hdF hmapsF hlittle hv
  rw [dist_eq_norm, hF0, sub_zero, dist_zero_right] at hmain
  have hR2 : M + ‖deriv f 0‖ * R ≤ 2 * M := by
    have h1 := mul_le_mul_of_nonneg_right hderiv (le_of_lt hR)
    rw [div_mul_cancel₀ M hR.ne'] at h1
    linarith
  calc ‖f v - deriv f 0 * v‖ = ‖F v‖ := by simp [hF]
    _ ≤ (M + ‖deriv f 0‖ * R) * (‖v‖ / R) ^ 2 := hmain
    _ ≤ 2 * M * (‖v‖ / R) ^ 2 := by
        apply mul_le_mul_of_nonneg_right hR2; positivity

end Work.EQ.AnalyticTaylor
