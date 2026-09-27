import Mathlib

namespace Work.EQ.Fatou

theorem radial_limit_factor {f h : ℂ → ℂ} {k : ℕ}
    (hfh : ∀ z ∈ Metric.ball (0:ℂ) 1, f z = z ^ k * h z) (θ : ℝ) :
    (Filter.Tendsto (fun r : ℝ => f (r * Complex.exp ((θ:ℂ) * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) ↔
      (Filter.Tendsto (fun r : ℝ => h (r * Complex.exp ((θ:ℂ) * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) := by
  set c : ℂ := Complex.exp ((θ:ℂ) * Complex.I) with hc
  have hc_norm : ‖c‖ = 1 := by
    rw [hc, Complex.norm_exp]
    have : ((θ:ℂ) * Complex.I).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hc_ne : c ≠ 0 := by
    intro h0; rw [h0] at hc_norm; simp at hc_norm
  have hc_pow_ne : c ^ k ≠ 0 := pow_ne_zero k hc_ne
  have hev_ball : ∀ᶠ r : ℝ in (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))),
      r * c ∈ Metric.ball (0:ℂ) 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (0:ℝ) < 1 by norm_num) (show (1:ℝ) < 1 + 1 by norm_num)]
      with r hr hr1
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hc_norm, mul_one,
      show ‖(r:ℂ)‖ = |r| from by simp, abs_of_pos hr.1]
    exact hr1
  have hev : (fun r : ℝ => f (r * c)) =ᶠ[nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))]
      (fun r : ℝ => (r * c) ^ k * h (r * c)) := by
    filter_upwards [hev_ball] with r hr
    exact hfh (r * c) hr
  have htend_c : Filter.Tendsto (fun r : ℝ => r * c)
      (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds c) := by
    have h1 : Filter.Tendsto (fun r : ℝ => (r:ℂ))
        (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds ((1:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const c
  have htend_A : Filter.Tendsto (fun r : ℝ => (r * c) ^ k)
      (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds (c ^ k)) := htend_c.pow k
  have htend_Ainv : Filter.Tendsto (fun r : ℝ => ((r * c) ^ k)⁻¹)
      (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds ((c ^ k)⁻¹)) :=
    htend_A.inv₀ hc_pow_ne
  have hA_ne : ∀ᶠ r : ℝ in (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))), (r * c) ^ k ≠ 0 :=
    htend_A.eventually_ne hc_pow_ne
  constructor
  · intro hF
    have hG : Filter.Tendsto (fun r : ℝ => (r * c) ^ k * h (r * c))
        (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds 0) := Filter.Tendsto.congr' hev hF
    have hGH : Filter.Tendsto
        (fun r : ℝ => ((r * c) ^ k * h (r * c)) * ((r * c) ^ k)⁻¹)
        (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds 0) := by
      have := hG.mul htend_Ainv
      simpa using this
    have heq2 : (fun r : ℝ => h (r * c)) =ᶠ[nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))]
        (fun r : ℝ => ((r * c) ^ k * h (r * c)) * ((r * c) ^ k)⁻¹) := by
      filter_upwards [hA_ne] with r hr
      rw [mul_comm ((r * c) ^ k) (h (r * c)), mul_inv_cancel_right₀ hr]
    exact Filter.Tendsto.congr' heq2.symm hGH
  · intro hH
    have hG : Filter.Tendsto (fun r : ℝ => (r * c) ^ k * h (r * c))
        (nhdsWithin (1:ℝ) (Set.Iio (1:ℝ))) (nhds 0) := by
      have := htend_A.mul hH
      simpa using this
    exact Filter.Tendsto.congr' hev.symm hG

end Work.EQ.Fatou
