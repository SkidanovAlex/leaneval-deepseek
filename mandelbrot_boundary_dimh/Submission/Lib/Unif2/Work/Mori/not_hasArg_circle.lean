import Mathlib
import Submission.Lib.Unif2.Work.Mori.Circle

namespace Work.Mori

/-- If `exp (x * I) = 1` for a real `x`, then `x` is an integer multiple of `2*pi`. -/
lemma exists_int_of_exp_eq_one {x : ℝ} (h : Complex.exp (((x : ℝ) : ℂ) * Complex.I) = 1) :
    ∃ n : ℤ, x = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  rw [h3] at h2
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, sub_zero, add_zero] at h2
  norm_num at h2
  linarith [h2]

/-- **The circle winds once around its centre.**  For `r > 0` the `1`-periodic curve
`Work.Mori.circle p r` (that is, `t ↦ p + r * exp (2 π i t)`) admits no continuous `1`-periodic
argument function with respect to `p`: `Commons.Topology.Winding.HasArg (circle p r) p` is false.

Route: if `θ` were such an argument, then `exp (i (θ t - 2 π t)) = 1` for all `t`
(`‖circle p r t - p‖ = r` computes the modulus), so `θ t - 2 π t ∈ 2 π ℤ` for all `t`; the set
`{t | θ t - 2 π t = θ 0}` is then clopen in `ℝ` (two elements of `2 π ℤ` at distance `< 2 π`
coincide), hence all of `ℝ`, contradicting `θ (1) = θ 0`.  This is the same argument as the existing
`Commons.Topology.Plane.not_hasArg_circ`, which treats only real centres: everything after the
modulus computation is centre-agnostic, so the proof can be copied with `c : ℝ` replaced by `p : ℂ`. -/
theorem not_hasArg_circle (p : ℂ) (r : ℝ) (hr : 0 < r) :
    ¬ Commons.Topology.Winding.HasArg (circle p r) p := by
  rintro ⟨θ, hθc, hθper, hθrep⟩
  -- the corrected argument `θ t - 2 π t` represents `1` on the unit circle
  have hexp : ∀ t : ℝ, Complex.exp (((θ t : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    intro t
    have h1 : circle p r t - p
        = (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
      simp [circle]
    have hnorm : (‖circle p r t - p‖ : ℂ) = (r : ℂ) := by
      rw [norm_circle_sub p hr.le t]
    have h := hθrep t
    rw [hnorm, h1] at h
    exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) h).symm
  -- so the drift `θ t - 2 π t` is always a multiple of `2 π`
  have hmem : ∀ t : ℝ, ∃ n : ℤ, θ t - 2 * Real.pi * t = 2 * Real.pi * n := by
    intro t
    apply exists_int_of_exp_eq_one
    rw [show (((θ t - 2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        = ((θ t : ℝ) : ℂ) * Complex.I - (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_sub, hexp t, div_self (Complex.exp_ne_zero _)]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- two multiples of `2 π` closer than `2 π` to each other coincide
  have hdisc : ∀ {x y : ℝ}, |x - y| < 2 * Real.pi →
      (∃ n : ℤ, x = 2 * Real.pi * n) → (∃ n : ℤ, y = 2 * Real.pi * n) → x = y := by
    intro x y hxy ⟨n1, h1⟩ ⟨n2, h2⟩
    have h3 : |2 * Real.pi * ((n1 : ℝ) - n2)| < 2 * Real.pi := by
      rw [show 2 * Real.pi * ((n1 : ℝ) - n2) = 2 * Real.pi * n1 - 2 * Real.pi * n2 by ring]
      rw [← h1, ← h2]; exact hxy
    rw [abs_mul, abs_of_pos h2pi] at h3
    have h4 : ((n1 : ℝ) - n2) = 0 := by
      by_contra hne
      have h5 : (n1 - n2 : ℤ) ≠ 0 := by
        intro hh
        exact hne (by rw [show n1 = n2 from by omega]; ring)
      have h6 : (1 : ℝ) ≤ |((n1 : ℝ) - n2)| := by
        have hsub : ((n1 : ℝ) - (n2 : ℝ)) = ((n1 - n2 : ℤ) : ℝ) := by push_cast; ring
        rw [hsub, ← Int.cast_abs, ← Int.cast_one]
        have hpos : (0 : ℤ) < |n1 - n2| := abs_pos.mpr h5
        exact_mod_cast (by omega : (1 : ℤ) ≤ |n1 - n2|)
      nlinarith [abs_nonneg ((n1 : ℝ) - n2)]
    rw [h1, h2]
    have : (n1 : ℝ) = n2 := by linarith
    rw [this]
  -- hence the drift is locally constant
  have hloc : IsLocallyConstant (fun t : ℝ => θ t - 2 * Real.pi * t) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hcont : Continuous (fun t : ℝ => θ t - 2 * Real.pi * t) :=
      hθc.sub (continuous_const.mul continuous_id)
    obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (2 * Real.pi) h2pi
    filter_upwards [Metric.ball_mem_nhds t hε] with u hu
    have hu' : dist (θ u - 2 * Real.pi * u) (θ t - 2 * Real.pi * t) < 2 * Real.pi := hε' hu
    rw [Real.dist_eq] at hu'
    exact hdisc hu' (hmem u) (hmem t)
  -- a locally constant function on the connected space `ℝ` is constant
  have hg10 : θ 1 - 2 * Real.pi = θ 0 := by
    have := hloc.apply_eq_of_isPreconnected (s := Set.univ) isPreconnected_univ
      (Set.mem_univ (1 : ℝ)) (Set.mem_univ (0 : ℝ))
    simpa using this
  have hper0 : θ (1 : ℝ) = θ 0 := by simpa using hθper 0
  linarith [hg10, hper0, Real.pi_pos]

end Work.Mori
