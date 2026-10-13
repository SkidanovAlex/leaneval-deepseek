import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem tendstoOfAbsLeCosDivSin {u : ℝ → ℝ} {K : ℝ}
    (h : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ| ≤ K * (Real.cos θ / Real.sin θ)) :
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hlt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- `cos θ / sin θ → 0` at `π/2`, hence so does `K * (cos θ / sin θ)`.
  have hb : Filter.Tendsto (fun θ => K * (Real.cos θ / Real.sin θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : Filter.Tendsto Real.cos
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 : Filter.Tendsto Real.cos (nhds (Real.pi / 2))
          (nhds (Real.cos (Real.pi / 2))) := Real.continuous_cos.continuousAt
      rw [Real.cos_pi_div_two] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have hs : Filter.Tendsto Real.sin
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
      have h1 : Filter.Tendsto Real.sin (nhds (Real.pi / 2))
          (nhds (Real.sin (Real.pi / 2))) := Real.continuous_sin.continuousAt
      rw [Real.sin_pi_div_two] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun θ => Real.cos θ / Real.sin θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (0 / 1)) :=
      hc.div hs one_ne_zero
    have h3 := h2.const_mul K
    simpa using h3
  -- the hypothesis holds eventually, since `(π/4, π/2)` is a left-neighbourhood of `π/2`.
  have hle : ∀ᶠ θ in (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))),
      |u θ| ≤ K * (Real.cos θ / Real.sin θ) := by
    filter_upwards [Ioo_mem_nhdsLT hlt] with θ hθ
    exact h θ hθ
  have hnorm : Filter.Tendsto (fun θ => |u θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Filter.Eventually.of_forall (fun θ => abs_nonneg (u θ))) hle
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa [Real.norm_eq_abs] using hnorm)

end Work.FTS.EllipticEst.remov.SourceBound
