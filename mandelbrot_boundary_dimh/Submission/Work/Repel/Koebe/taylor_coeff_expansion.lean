import Mathlib

/-!
# Taylor expansion of a function analytic on the unit disc

For `φ` analytic on the open unit disc with `φ 0 = 0` we exhibit its Taylor coefficients
`c k = (iteratedDeriv k φ 0) / k!` and prove the three properties used downstream:

* the (formal) power series `∑ c k * u ^ k` sums to `φ u` for every `u` of modulus `< 1`;
* `c 0 = 0` (because `φ 0 = 0`) and `c 1 = deriv φ 0`;
* `∑ ‖c k‖ / r ^ k` converges for every `r > 1`, i.e. the radius of convergence of the
  Taylor series at the origin is at least `1`.

The last point is Cauchy's estimate on a circle of radius `ρ` with `1/r < ρ < 1`, which gives
`‖c k‖ ≤ C / ρ ^ k`, hence `‖c k‖ / r ^ k ≤ C / (ρ * r) ^ k` with `ρ * r > 1`.
-/

namespace Work.Repel.Koebe

theorem taylor_coeff_expansion {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 1)) (h0 : φ 0 = 0) :
    ∃ c : ℕ → ℂ,
      c 0 = 0 ∧ c 1 = deriv φ 0 ∧
      (∀ u : ℂ, u ≠ 0 → ‖u‖ < 1 → HasSum (fun k : ℕ => c k * u ^ k) (φ u)) ∧
      (∀ r : ℝ, 1 < r → Summable (fun k : ℕ => ‖c k‖ / r ^ k)) := by
  have hdiff : DifferentiableOn ℂ φ (Metric.ball 0 1) := hφ.differentiableOn
  refine ⟨fun k => ((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k φ 0, ?_, ?_, ?_, ?_⟩
  · simp [iteratedDeriv_zero, h0]
  · simp [iteratedDeriv_one]
  · intro u _ hu1
    have h := Complex.hasSum_taylorSeries_on_ball (f := φ) (c := 0) (r := 1) hdiff
      (z := u) (by rwa [Metric.mem_ball, dist_zero_right])
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h
  · intro r hr
    set ρ : ℝ := (1 + r⁻¹) / 2 with hρ
    have hrpos : 0 < r := lt_trans zero_lt_one hr
    have hρpos : 0 < ρ := by rw [hρ]; positivity
    have hρlt : ρ < 1 := by
      rw [hρ]
      have h : r⁻¹ < 1 := by rw [inv_lt_one₀ hrpos]; exact hr
      linarith
    have hρr : 1 < ρ * r := by
      have hmul : ρ * r = (r + 1) / 2 := by rw [hρ]; field_simp
      rw [hmul]; linarith
    have hdc : DiffContOnCl ℂ φ (Metric.ball 0 ρ) :=
      hdiff.diffContOnCl_ball (Metric.closedBall_subset_ball hρlt)
    have hcont : ContinuousOn φ (Metric.sphere 0 ρ) :=
      hdiff.continuousOn.mono (fun z hz => by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        linarith)
    obtain ⟨C, hC⟩ := (isCompact_sphere (0:ℂ) ρ).exists_bound_of_continuousOn hcont
    have hCauchy : ∀ k : ℕ, ‖iteratedDeriv k φ 0‖ ≤ (Nat.factorial k : ℝ) * C / ρ ^ k :=
      fun k => Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρpos hdc hC
    have hbound : ∀ k : ℕ, ‖((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k φ 0‖ ≤ C / ρ ^ k := by
      intro k
      have h1 : ‖((Nat.factorial k : ℂ))⁻¹‖ = (((Nat.factorial k : ℕ) : ℝ))⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      calc ‖((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k φ 0‖
          = ‖((Nat.factorial k : ℂ))⁻¹‖ * ‖iteratedDeriv k φ 0‖ := norm_mul _ _
        _ ≤ ((Nat.factorial k : ℝ))⁻¹ * ((Nat.factorial k : ℝ) * C / ρ ^ k) := by
              apply mul_le_mul (le_of_eq h1) (hCauchy k) (norm_nonneg _)
              positivity
        _ = C / ρ ^ k := by field_simp
    have hgeom : Summable (fun k : ℕ => C * ((ρ * r)⁻¹) ^ k) := by
      have h1 : ‖((ρ * r)⁻¹ : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity), inv_lt_one₀ (by positivity)]
        exact hρr
      exact (summable_geometric_of_norm_lt_one h1).mul_left C
    refine Summable.of_nonneg_of_le (fun k => div_nonneg (norm_nonneg _) (by positivity)) ?_ hgeom
    intro k
    calc ‖((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k φ 0‖ / r ^ k
        ≤ (C / ρ ^ k) / r ^ k := by gcongr; exact hbound k
      _ = C * ((ρ * r)⁻¹) ^ k := by
            have h2 : ((ρ * r)⁻¹) ^ k = (ρ ^ k)⁻¹ * (r ^ k)⁻¹ := by
              rw [inv_pow, mul_pow, mul_inv]
            rw [h2, div_eq_mul_inv, div_eq_mul_inv]
            ring

end Work.Repel.Koebe
