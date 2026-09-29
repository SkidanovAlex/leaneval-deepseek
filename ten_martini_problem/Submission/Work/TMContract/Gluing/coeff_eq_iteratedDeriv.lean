import Mathlib

open Filter
open scoped Topology

namespace Work.TMContract.Gluing

/-- If a function `h ↦ Φ (E₀ + h, y)` has a pointwise power series expansion
`Φ (E₀ + h, y) = ∑ₙ cₙ(y) hⁿ` on the open interval `|h| < r`, with `r > 0`, then the
coefficients `cₙ(y)` are exactly the Taylor coefficients of the function at `0`, i.e.
`cₙ(y) = fⁿ(0)/n!`.

The proof packages the given pointwise expansion as a `HasFPowerSeriesAt` datum for the
formal scalar series `∑ cₙ(y) xⁿ`, transfers it to the concrete function via eventual
equality on the ball `|h| < r`, and then extracts the coefficient using
`HasFPowerSeriesOnBall.factorial_smul`. -/
theorem coeff_eq_iteratedDeriv {Φ : ℝ × ℝ → ℝ} {E₀ x₀ r C : ℝ} {c : ℕ → ℝ → ℝ}
    (hr : 0 < r)
    (hbd : ∀ m y, y ∈ Set.Icc (x₀ - r) (x₀ + r) → |c m y| ≤ C * (1 / r) ^ m)
    (hexp : ∀ h' y, |h'| < r → |y - x₀| < r → HasSum (fun m => c m y * h' ^ m) (Φ (E₀ + h', y))) :
    ∀ m y, |y - x₀| < r →
      c m y = iteratedDeriv m (fun h : ℝ => Φ (E₀ + h, y)) 0 / (m.factorial : ℝ) := by
  intro m y hy
  set f : ℝ → ℝ := fun h => Φ (E₀ + h, y) with hf_def
  set p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ (fun n => c n y)
    with hp_def
  -- The scalar series has positive radius of convergence: the bound `hbd` dominates it on
  -- the closed ball of radius `r`.
  have hr_pos_radius : 0 < p.radius := by
    let r₀ : NNReal := ⟨r, hr.le⟩
    have hcoe : (r₀ : ℝ) = r := rfl
    have hle : (r₀ : ENNReal) ≤ p.radius := by
      apply FormalMultilinearSeries.le_radius_of_bound p C (r := r₀)
      intro n
      have hyIcc : y ∈ Set.Icc (x₀ - r) (x₀ + r) := by
        rw [Set.mem_Icc]
        exact ⟨by linarith [(abs_lt.mp hy).1], by linarith [(abs_lt.mp hy).2]⟩
      have hn : ‖p n‖ = |c n y| := by
        rw [hp_def, FormalMultilinearSeries.ofScalars_norm]
        exact Real.norm_eq_abs _
      rw [hn, hcoe]
      calc |c n y| * r ^ n ≤ (C * (1 / r) ^ n) * r ^ n :=
            mul_le_mul_of_nonneg_right (hbd n y hyIcc) (by positivity)
        _ = C := by
            rw [mul_assoc, ← mul_pow, one_div_mul_cancel (ne_of_gt hr), one_pow, mul_one]
    have h0 : (0 : ENNReal) < (r₀ : ENNReal) := by
      rw [ENNReal.coe_pos]; exact hr
    exact lt_of_lt_of_le h0 hle
  -- The formal series represents its own sum near `0`.
  have hp_series : HasFPowerSeriesAt p.sum p 0 :=
    ⟨p.radius, p.hasFPowerSeriesOnBall hr_pos_radius⟩
  -- On the ball `|h| < r`, the sum of the series coincides with `f`.
  have hfg : p.sum =ᶠ[𝓝 0] f := by
    have hball : Metric.ball (0 : ℝ) r ∈ 𝓝 0 :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, Real.dist_eq] using hr)
    apply Filter.mem_of_superset hball
    intro h' hh'
    have hh'lt : |h'| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hh'
    have h1 : (fun n => p n (fun _ => h')) = fun n => c n y * h' ^ n := by
      funext n
      rw [hp_def, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    have htsum : (∑' n, p n (fun _ => h')) = Φ (E₀ + h', y) := by
      rw [h1]; exact (hexp h' y hh'lt hy).tsum_eq
    show p.sum h' = f h'
    rw [hf_def]
    simpa only [FormalMultilinearSeries.sum] using htsum
  -- Transfer the power series to `f`.
  have hp_f : HasFPowerSeriesAt f p 0 := hp_series.congr hfg
  obtain ⟨ρ, hρ⟩ := hp_f
  have hp1 : p m (fun _ => (1 : ℝ)) = c m y := by
    rw [hp_def, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, one_pow, mul_one]
  have hkey : (m.factorial : ℝ) * c m y = iteratedDeriv m f 0 := by
    have h := hρ.factorial_smul (1 : ℝ) m
    rw [hp1] at h
    rw [← iteratedDeriv_eq_iteratedFDeriv] at h
    rw [nsmul_eq_mul] at h
    exact h
  rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero m), mul_comm]
  exact hkey

end Work.TMContract.Gluing
