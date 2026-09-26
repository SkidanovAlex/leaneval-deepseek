import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Filter Topology

open scoped Topology

namespace Commons.Analysis.Calculus

/-- For a C¹ (real-valued) function at a point, the difference quotient over
any two distinct points tending to the point tends to the derivative there:
`(f (x n) − f (y n)) / (x n − y n) → deriv f x₀` whenever `x n`, `y n → x₀`
and `x n ≠ y n` eventually. -/
theorem tendsto_slope_of_contDiffAt {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 1 f x₀)
    {x y : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 x₀))
    (hxy : ∀ᶠ n in atTop, x n ≠ y n) :
    Tendsto (fun n : ℕ => (f (x n) - f (y n)) / (x n - y n)) atTop (𝓝 (deriv f x₀)) := by
  rcases contDiffAt_one_iff.mp hf with ⟨f', u, hu_nhds, hu_cont, hu_fderiv⟩
  let d : ℝ → ℝ := fun t => (f' t) 1
  have hd_eq_deriv : deriv f x₀ = d x₀ := by
    have hx0u : x₀ ∈ u := mem_of_mem_nhds hu_nhds
    simpa [d] using (hu_fderiv x₀ hx0u).hasDerivAt.deriv
  rw [hd_eq_deriv]
  have hf'_contAt : ContinuousAt f' x₀ := hu_cont.continuousAt hu_nhds
  rcases Metric.mem_nhds_iff.mp hu_nhds with ⟨r, hr, hball_u⟩
  have hfd : ∀ t ∈ u, HasDerivAt f (d t) t := by
    intro t ht
    simpa [d] using (hu_fderiv t ht).hasDerivAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  rcases Metric.tendsto_nhds_nhds.mp hf'_contAt.tendsto (ε / 2) hε2 with ⟨δ1, hδ10, hδ1⟩
  let δ : ℝ := min δ1 r
  have hδpos : 0 < δ := lt_min hδ10 hr
  have hδ_le_δ1 : δ ≤ δ1 := min_le_left δ1 r
  have hδ_le_r : δ ≤ r := min_le_right δ1 r
  have hxev : ∀ᶠ n in atTop, x n ∈ Metric.ball x₀ δ := by
    have hxδ := (Metric.tendsto_nhds.mp hx) δ hδpos
    filter_upwards [hxδ] with n hn
    exact hn
  have hyev : ∀ᶠ n in atTop, y n ∈ Metric.ball x₀ δ := by
    have hyδ := (Metric.tendsto_nhds.mp hy) δ hδpos
    filter_upwards [hyδ] with n hn
    exact hn
  let c : ℝ := d x₀
  have hev2 : ∀ᶠ n in atTop, |(f (x n) - f (y n)) / (x n - y n) - c| ≤ ε / 2 := by
    filter_upwards [hxev, hyev, hxy] with n hxn hyn hne
    let H : ℝ → ℝ := fun t => f t - c * t
    have hcderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c * t) c t := by
      intro t
      simpa using (hasDerivAt_id t).const_mul c
    have hMVT : ‖H (y n) - H (x n)‖ ≤ (ε / 2) * ‖y n - x n‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Metric.ball x₀ δ)
        (f := H) (f' := fun t => d t - c) (C := ε / 2) ?_ ?_ (convex_ball x₀ δ) hxn hyn
      · intro t ht
        have htu : t ∈ u := hball_u (Metric.ball_subset_ball hδ_le_r ht)
        have hft : HasDerivAt f (d t) t := hfd t htu
        have hHt : HasDerivAt (fun t : ℝ => f t - c * t) (d t - c) t := hft.sub (hcderiv t)
        have hH : HasDerivAt H (d t - c) t := by simpa [H] using hHt
        exact hH.hasDerivWithinAt
      · intro t ht
        have htδ1 : dist t x₀ < δ1 := lt_of_lt_of_le (by simpa [Metric.mem_ball] using ht) hδ_le_δ1
        have hdlt : dist (f' t) (f' x₀) < ε / 2 := hδ1 htδ1
        have hop : ‖f' t - f' x₀‖ < ε / 2 := by simpa [dist_eq_norm] using hdlt
        have hle : ‖(f' t - f' x₀) 1‖ ≤ ε / 2 := by
          have hbnd := (f' t - f' x₀).le_opNorm (1 : ℝ)
          calc
            ‖(f' t - f' x₀) 1‖ ≤ ‖f' t - f' x₀‖ * ‖(1 : ℝ)‖ := hbnd
            _ = ‖f' t - f' x₀‖ := by simp
            _ ≤ ε / 2 := le_of_lt hop
        simpa [d, c, sub_apply] using hle
    have hmain : |(f (x n) - f (y n)) - c * (x n - y n)| ≤ (ε / 2) * |x n - y n| := by
      calc
        |(f (x n) - f (y n)) - c * (x n - y n)|
            = |(f (y n) - c * y n) - (f (x n) - c * x n)| := by
                rw [show (f (y n) - c * y n) - (f (x n) - c * x n) =
                      -((f (x n) - f (y n)) - c * (x n - y n)) by ring]
                rw [abs_neg]
        _ ≤ (ε / 2) * |y n - x n| := by
                simpa [H] using hMVT
        _ = (ε / 2) * |x n - y n| := by rw [abs_sub_comm]
    have hb : x n - y n ≠ 0 := sub_ne_zero.mpr hne
    have habs : |x n - y n| ≠ 0 := abs_ne_zero.mpr hb
    calc
      |(f (x n) - f (y n)) / (x n - y n) - c|
          = |((f (x n) - f (y n)) - c * (x n - y n)) / (x n - y n)| := by
              congr 1
              field_simp [hb]
      _ = |(f (x n) - f (y n)) - c * (x n - y n)| / |x n - y n| := by rw [abs_div]
      _ ≤ ((ε / 2) * |x n - y n|) / |x n - y n| := by
              exact div_le_div_of_nonneg_right hmain (abs_nonneg (x n - y n))
      _ = ε / 2 := by field_simp [habs]
  have hev : ∀ᶠ n in atTop, |(f (x n) - f (y n)) / (x n - y n) - d x₀| < ε := by
    filter_upwards [hev2] with n hn
    simpa [c] using lt_of_le_of_lt hn (by linarith)
  simpa [Real.dist_eq] using hev

end Commons.Analysis.Calculus