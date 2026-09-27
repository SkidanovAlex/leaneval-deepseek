import Mathlib

/-! Auxiliary lemmas for the Parseval identity `integral_normSq_eq_tsum`:
orthogonality of the characters `θ ↦ e^{i n θ}` on `[0, 2π]`, and absolute summability of
the coefficients `‖a n‖ * ρ^n` for a power series converging on a larger disc. -/

namespace Work.EQ.Fatou

open Complex MeasureTheory

/-- Orthogonality of the complex exponentials on a full period:
`∫_0^{2π} e^{i k θ} dθ = 2π` if `k = 0` and `0` otherwise, for integral `k`. -/
theorem intervalIntegral_cexp_int_mul (k : ℤ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, Complex.exp ((k:ℂ) * (θ:ℂ) * Complex.I)
      = if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hc : ((k:ℂ) * Complex.I) ≠ 0 := by
      simp [hk]
    have hcongr : (fun θ : ℝ => Complex.exp ((k:ℂ) * (θ:ℂ) * Complex.I))
        = fun θ : ℝ => Complex.exp (((k:ℂ) * Complex.I) * (θ:ℂ)) := by
      funext θ; congr 1; ring
    rw [hcongr, integral_exp_mul_complex hc]
    have hexp : Complex.exp (((k:ℂ) * Complex.I) * (2*Real.pi : ℂ)) = 1 := by
      have : ((k:ℂ) * Complex.I) * (2 * (Real.pi : ℂ)) = (k:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by ring
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I k
    simp [hexp]

/-- Orthogonality of the characters indexed by naturals, in the form needed for Parseval. -/
theorem intervalIntegral_cexp_mul_conj (n m : ℕ) :
    ∫ θ in (0:ℝ)..2 * Real.pi,
        Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I) * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I))
      = if n = m then (2 * Real.pi : ℂ) else 0 := by
  have hfun : (fun θ : ℝ => Complex.exp ((n:ℂ) * (θ:ℂ) * Complex.I)
        * Complex.exp (-((m:ℂ) * (θ:ℂ) * Complex.I)))
      = fun θ : ℝ => Complex.exp ((((n:ℤ) - m : ℤ) : ℂ) * (θ:ℂ) * Complex.I) := by
    funext θ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, intervalIntegral_cexp_int_mul]
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by exact_mod_cast (sub_eq_zero.mp hc : (n:ℤ) = m))

/-- **Absolute convergence of the coefficients at a strictly smaller radius.**
If the power series `∑ aₙ zⁿ` converges on the disc of radius `R`, then for any `0 < ρ < R`
the series `∑ ‖aₙ‖ ρⁿ` (and its squares `∑ ‖aₙ‖² ρ^{2n}`) converge. -/
theorem summable_norm_mul_pow {a : ℕ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : ρ < R)
    (ha : ∀ z ∈ Metric.ball (0:ℂ) R, ∃ w : ℂ, HasSum (fun n => a n * z^n) w) :
    Summable (fun n => ‖a n‖ * ρ^n) ∧ Summable (fun n => ‖a n‖^2 * ρ^(2*n)) := by
  obtain ⟨r, hρr, hrR⟩ := exists_between hR
  have hr : 0 < r := lt_trans hρ hρr
  have hmem : (r:ℂ) ∈ Metric.ball (0:ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact hrR
  obtain ⟨w, hw⟩ := ha (r:ℂ) hmem
  have hs1 : Summable (fun n => a n * (r:ℂ)^n) := hw.summable
  have hs2 : Summable (fun n => ‖a n * (r:ℂ)^n‖) := hs1.norm
  have hs3 : Summable (fun n => ‖a n‖ * r^n) := hs2.congr (fun n => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le])
  have hle : ∀ n, ‖a n‖ * ρ^n ≤ ‖a n‖ * r^n := by
    intro n
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hρr.le n) (norm_nonneg _)
  have hnonneg : ∀ n, 0 ≤ ‖a n‖ * ρ^n :=
    fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le n)
  have hsumρ : Summable (fun n => ‖a n‖ * ρ^n) := Summable.of_nonneg_of_le hnonneg hle hs3
  refine ⟨hsumρ, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hsumρ.mul_left (∑' n, ‖a n‖ * ρ^n))
  · exact mul_nonneg (sq_nonneg _) (pow_nonneg hρ.le _)
  · have hle' : ‖a n‖ * ρ^n ≤ ∑' m, ‖a m‖ * ρ^m :=
      hsumρ.le_tsum n (fun j _ => hnonneg j)
    have hn : 0 ≤ ‖a n‖ * ρ^n := hnonneg n
    calc ‖a n‖^2 * ρ^(2*n) = (‖a n‖ * ρ^n)^2 := by
          rw [mul_pow, ← pow_mul, mul_comm 2 n]
      _ = (‖a n‖ * ρ^n) * (‖a n‖ * ρ^n) := by ring
      _ ≤ (∑' m, ‖a m‖ * ρ^m) * (‖a n‖ * ρ^n) := mul_le_mul_of_nonneg_right hle' hn

end Work.EQ.Fatou
