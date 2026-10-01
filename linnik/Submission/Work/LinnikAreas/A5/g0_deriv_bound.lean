import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

open Filter
open scoped Topology

namespace Work.LinnikAreas.A5

/-!
# The derivative bound `|g₀'| ≤ 1/K` on `[0,K]`

For the λ → 0 test function `g0 K t = if t ≤ K then (K−t)/K else 0` of HB Lemma 13.3:

* on the open interval `(-∞, K)` the function coincides with the affine map `t ↦ (K−t)/K`,
  so its derivative there is the constant `−1/K`, of norm `1/K`;
* at the right endpoint `t = K` the one-sided slopes are `−1/K` (from the left) and `0`
  (from the right), so `g0 K` is not differentiable at `K` and `deriv (g0 K) K = 0` by
  `deriv_zero_of_not_differentiableAt`, whence the bound holds there too (as `0 < K`).

The two facts are proved below as `g0_deriv_of_lt` and `not_differentiableAt_g0`, and the
requested bound `g0_deriv_bound` is their immediate consequence.
-/

/-- On `(-∞, K)` the test function `g0 K` agrees with the affine map `t ↦ (K−t)/K`, so its
derivative is the constant `−1/K`. -/
lemma g0_deriv_of_lt {K t : ℝ} (h : t < K) : deriv (g0 K) t = -(1 / K) := by
  have hev : (fun s : ℝ => (K - s) / K) =ᶠ[𝓝 t] g0 K := by
    filter_upwards [isOpen_Iio.mem_nhds h] with s hs
    exact (g0_of_le hs.le).symm
  rw [← hev.deriv_eq]
  rw [deriv_div_const]
  have h1 : deriv (fun s : ℝ => K - s) t = -1 := by
    simp
  rw [h1]
  ring

/-- At the right endpoint `t = K` the one-sided slopes of `g0 K` differ (`−1/K` against `0`),
so `g0 K` is not differentiable at `K`.  This forces `deriv (g0 K) K = 0`. -/
lemma not_differentiableAt_g0 {K : ℝ} (hK : 0 < K) : ¬ DifferentiableAt ℝ (g0 K) K := by
  intro hd
  -- the right difference quotients are identically `0`
  have hright : deriv (g0 K) K = 0 := by
    have h := hd.hasDerivAt.tendsto_slope_zero_right
    have hev : (fun t : ℝ => t⁻¹ • (g0 K (K + t) - g0 K K))
        =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      have hle : K ≤ K + t := by linarith
      rw [g0_of_ge hle, g0_of_ge le_rfl]
      simp
    have h' : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[>] (0:ℝ))
        (𝓝 (deriv (g0 K) K)) := h.congr' hev
    exact tendsto_nhds_unique h' tendsto_const_nhds
  -- the left difference quotients are identically `−1/K`
  have hleft : deriv (g0 K) K = -(1 / K) := by
    have h := hd.hasDerivAt.tendsto_slope_zero_left
    have hev : (fun t : ℝ => t⁻¹ • (g0 K (K + t) - g0 K K))
        =ᶠ[𝓝[<] (0:ℝ)] (fun _ => (-(1 / K) : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t < 0 := ht
      have hle : K + t ≤ K := by linarith
      have hne : t ≠ 0 := ne_of_lt ht0
      have hKne : K ≠ 0 := ne_of_gt hK
      rw [g0_of_le hle, g0_of_ge le_rfl]
      simp only [sub_zero, smul_eq_mul]
      field_simp
      ring
    have h' : Tendsto (fun _ : ℝ => (-(1 / K) : ℝ)) (𝓝[<] (0:ℝ))
        (𝓝 (deriv (g0 K) K)) := h.congr' hev
    exact tendsto_nhds_unique h' tendsto_const_nhds
  have h0 : (0 : ℝ) = -(1 / K) := by rw [← hright, hleft]
  have hpos : (0 : ℝ) < 1 / K := one_div_pos.mpr hK
  linarith

/-- The derivative bound for the λ → 0 test function `g0 K t = if t ≤ K then (K−t)/K else 0`
(`Work.LinnikAreas.A5.g0`): `‖g0 K'‖ ≤ 1/K` on `[0,K]`.  On `[0,K)` the function agrees near each
point with the affine `(K−t)/K`, whose derivative is the constant `−1/K` with norm `1/K`; at the
right endpoint `t = K` the function is *not* differentiable (one-sided slopes `−1/K` and `0`), so
`deriv (g0 K) K = 0` by `deriv_zero_of_not_differentiableAt`, and the bound holds there. -/
theorem g0_deriv_bound (K : ℝ) (hK : 0 < K) :
    ∀ t ∈ Set.Icc (0 : ℝ) K, ‖deriv (Work.LinnikAreas.A5.g0 K) t‖ ≤ 1 / K := by
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · rw [g0_deriv_of_lt hlt, norm_neg, Real.norm_of_nonneg (one_div_nonneg.mpr hK.le)]
  · rw [heq, deriv_zero_of_not_differentiableAt (not_differentiableAt_g0 hK), norm_zero]
    exact one_div_nonneg.mpr hK.le

end Work.LinnikAreas.A5
