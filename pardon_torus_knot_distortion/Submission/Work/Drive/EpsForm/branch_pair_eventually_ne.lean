import Mathlib

namespace Work.Drive.EpsForm

open scoped Topology
open Filter

/-- **Two branches with a non-vanishing linear separation stay separated for small `t > 0`.** `F` and `G` are `C¹`; `x`, `x'` are critical points of `F`; `y`, `y'` are curves through `x`, `x'` that are Lipschitz at `0` with common constant `C` (`‖y t - x‖ ≤ C * |t|`, similarly for `y'`); and the two critical points are separated to first order: `F x ≠ F x'` or `G x ≠ G x'`. Then for all small `t > 0`, `F (y t) + t * G (y t) ≠ F (y' t) + t * G (y' t)`.

Proof. `y`, `y'` are continuous at `0` with `y 0 = x`, `y' 0 = x'` (the Lipschitz bound at `t = 0`). If `F x ≠ F x'` then the difference has nonzero limit `F x - F x'`. Otherwise `F x = F x'` and `G x ≠ G x'`, and
`v t / t = (F (y t) - F x)/t - (F (y' t) - F x')/t + (G (y t) - G (y' t))`
with `(F (y t) - F x)/t → 0` (because `fderiv ℝ F x = 0`, `F` differentiable at `x`, `‖y t - x‖ = O(t)`: use `HasFDerivAt.isLittleO` + `Asymptotics.IsLittleO.trans_isBigO` + `Asymptotics.IsBigO.of_bound`, or `Convex.norm_image_sub_le_of_norm_fderivWithin_le` on a ball around `x`) and `G (y t) - G (y' t) → G x - G x' ≠ 0`; hence `v t / t` is eventually nonzero on `𝓝[>] 0`. -/
theorem branch_pair_eventually_ne (F G : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    {x x' : ℝ × ℝ} (hx : fderiv ℝ F x = 0) (hx' : fderiv ℝ F x' = 0)
    {y y' : ℝ → ℝ × ℝ} {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hy : ∀ t : ℝ, |t| < δ → ‖y t - x‖ ≤ C * |t|)
    (hy' : ∀ t : ℝ, |t| < δ → ‖y' t - x'‖ ≤ C * |t|)
    (hne : F x ≠ F x' ∨ G x ≠ G x') :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), F (y t) + t * G (y t) ≠ F (y' t) + t * G (y' t) := by
  have hFc : Continuous F := hF.continuous
  have hGc : Continuous G := hG.continuous
  -- eventually `|t| < δ`
  have hδev : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), |t| < δ := by
    have : Metric.ball (0:ℝ) δ ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds 0 hδ
    filter_upwards [this] with t ht
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using ht
  have hCtend : Tendsto (fun t : ℝ => C * |t|) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hcont : Continuous (fun t : ℝ => C * |t|) := continuous_const.mul continuous_abs
    simpa using hcont.tendsto (0:ℝ)
  -- the two curves converge to their (critical) base points
  have hy_tend : Tendsto y (𝓝 (0:ℝ)) (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero'
    · filter_upwards with t; positivity
    · filter_upwards [hδev] with t ht; exact hy t ht
    · exact hCtend
  have hy'_tend : Tendsto y' (𝓝 (0:ℝ)) (𝓝 x') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero'
    · filter_upwards with t; positivity
    · filter_upwards [hδev] with t ht; exact hy' t ht
    · exact hCtend
  by_cases hFF : F x = F x'
  · -- `F x = F x'`: the leading term in `t` is `t * (G x - G x') ≠ 0`.
    have hGG : G x ≠ G x' := by
      rcases hne with h | h
      · exact absurd hFF h
      · exact h
    -- `F` is differentiable at the two critical points, with vanishing derivative
    have hFx_der : HasFDerivAt F (0 : (ℝ × ℝ) →L[ℝ] ℝ) x := by
      have hd := (hF.differentiable_one.differentiableAt (x := x)).hasFDerivAt
      rwa [hx] at hd
    have hFx'_der : HasFDerivAt F (0 : (ℝ × ℝ) →L[ℝ] ℝ) x' := by
      have hd := (hF.differentiable_one.differentiableAt (x := x')).hasFDerivAt
      rwa [hx'] at hd
    -- `F (y t) - F x = o(t)` and `F (y' t) - F x' = o(t)`
    have hφ₁ : (fun t : ℝ => F (y t) - F x) =o[𝓝 (0:ℝ)] (fun t : ℝ => t) := by
      have h1 : (fun z : ℝ × ℝ => F z - F x) =o[𝓝 x] (fun z : ℝ × ℝ => z - x) := by
        simpa using hFx_der.isLittleO
      have h2 := h1.comp_tendsto hy_tend
      have h3 : (fun t : ℝ => y t - x) =O[𝓝 (0:ℝ)] (fun t : ℝ => t) := by
        apply Asymptotics.IsBigO.of_bound C
        filter_upwards [hδev] with t ht
        simpa [Real.norm_eq_abs] using hy t ht
      exact h2.trans_isBigO h3
    have hφ₂ : (fun t : ℝ => F (y' t) - F x') =o[𝓝 (0:ℝ)] (fun t : ℝ => t) := by
      have h1 : (fun z : ℝ × ℝ => F z - F x') =o[𝓝 x'] (fun z : ℝ × ℝ => z - x') := by
        simpa using hFx'_der.isLittleO
      have h2 := h1.comp_tendsto hy'_tend
      have h3 : (fun t : ℝ => y' t - x') =O[𝓝 (0:ℝ)] (fun t : ℝ => t) := by
        apply Asymptotics.IsBigO.of_bound C
        filter_upwards [hδev] with t ht
        simpa [Real.norm_eq_abs] using hy' t ht
      exact h2.trans_isBigO h3
    -- hence the `F`-difference is `o(t)`
    have hA : (fun t : ℝ => F (y t) - F (y' t)) =o[𝓝 (0:ℝ)] (fun t : ℝ => t) := by
      refine (hφ₁.sub hφ₂).congr_left ?_
      intro t
      rw [hFF]
      ring
    have hL : G x - G x' ≠ 0 := sub_ne_zero.mpr hGG
    have hA' : (fun t : ℝ => F (y t) - F (y' t)) =o[𝓝[>] (0:ℝ)] (fun t : ℝ => t) :=
      hA.mono nhdsWithin_le_nhds
    have hdiv : Tendsto (fun t : ℝ => (F (y t) - F (y' t)) / t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      hA'.tendsto_div_nhds_zero
    have hBy : Tendsto (fun t : ℝ => G (y t)) (𝓝 (0:ℝ)) (𝓝 (G x)) := (hGc.tendsto x).comp hy_tend
    have hBy' : Tendsto (fun t : ℝ => G (y' t)) (𝓝 (0:ℝ)) (𝓝 (G x')) := (hGc.tendsto x').comp hy'_tend
    have hB : Tendsto (fun t : ℝ => G (y t) - G (y' t)) (𝓝[>] (0:ℝ)) (𝓝 (G x - G x')) :=
      (hBy.sub hBy').mono_left nhdsWithin_le_nhds
    have hD : Tendsto (fun t : ℝ => (F (y t) - F (y' t)) / t + (G (y t) - G (y' t)))
        (𝓝[>] (0:ℝ)) (𝓝 (0 + (G x - G x'))) := hdiv.add hB
    have hDev : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
        (F (y t) - F (y' t)) / t + (G (y t) - G (y' t)) ≠ 0 :=
      hD.eventually_ne (by simpa using hL)
    have htne : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ne_of_gt ht
    filter_upwards [hDev, htne] with t hDt ht0
    intro hcontra
    have htd : t * ((F (y t) - F (y' t)) / t + (G (y t) - G (y' t)))
        = F (y t) + t * G (y t) - (F (y' t) + t * G (y' t)) := by
      field_simp
      ring
    have hzero : t * ((F (y t) - F (y' t)) / t + (G (y t) - G (y' t))) = 0 := by
      rw [htd, sub_eq_zero.mpr hcontra]
    rcases mul_eq_zero.mp hzero with h | h
    · exact ht0 h
    · exact hDt h
  · -- `F x ≠ F x'`: the difference has the nonzero limit `F x - F x'`.
    have hFF' : F x ≠ F x' := hFF
    have hu : Tendsto (fun t : ℝ => F (y t) + t * G (y t)) (𝓝 (0:ℝ)) (𝓝 (F x)) := by
      have hFy : Tendsto (fun t : ℝ => F (y t)) (𝓝 (0:ℝ)) (𝓝 (F x)) :=
        (hFc.tendsto x).comp hy_tend
      have hGy : Tendsto (fun t : ℝ => G (y t)) (𝓝 (0:ℝ)) (𝓝 (G x)) :=
        (hGc.tendsto x).comp hy_tend
      have := hFy.add (tendsto_id.mul hGy)
      simpa using this
    have hu' : Tendsto (fun t : ℝ => F (y' t) + t * G (y' t)) (𝓝 (0:ℝ)) (𝓝 (F x')) := by
      have hFy : Tendsto (fun t : ℝ => F (y' t)) (𝓝 (0:ℝ)) (𝓝 (F x')) :=
        (hFc.tendsto x').comp hy'_tend
      have hGy : Tendsto (fun t : ℝ => G (y' t)) (𝓝 (0:ℝ)) (𝓝 (G x')) :=
        (hGc.tendsto x').comp hy'_tend
      have := hFy.add (tendsto_id.mul hGy)
      simpa using this
    have hlim : Tendsto (fun t : ℝ => F (y t) + t * G (y t) - (F (y' t) + t * G (y' t)))
        (𝓝 (0:ℝ)) (𝓝 (F x - F x')) := hu.sub hu'
    have hEv : ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
        F (y t) + t * G (y t) - (F (y' t) + t * G (y' t)) ≠ 0 :=
      hlim.eventually_ne (sub_ne_zero.mpr hFF')
    have hEv' : ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
        F (y t) + t * G (y t) ≠ F (y' t) + t * G (y' t) :=
      hEv.mono (fun t ht => sub_ne_zero.mp ht)
    exact hEv'.filter_mono nhdsWithin_le_nhds

end Work.Drive.EpsForm
