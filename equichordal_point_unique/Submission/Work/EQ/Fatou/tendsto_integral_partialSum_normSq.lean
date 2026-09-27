import Mathlib
import Submission.Work.EQ.Fatou.ParsevalAux

/-!
# Convergence of the integrals of the squared partial sums of a power series

If the power series `∑ aₙ zⁿ` converges on the disc of radius `R` (with sum `h z`), then
for every radius `ρ < R` the integrals over the circle `|z| = ρ` of `‖∑_{n<N} aₙ zⁿ‖²`
converge to the integral of `‖h‖²` on that circle.

The proof is the dominated convergence theorem: on the circle the partial sums are
uniformly bounded by `∑ ‖aₙ‖ ρⁿ < ∞` (which is summable by `summable_norm_mul_pow`), and
they converge pointwise to `h` because the circle of radius `ρ` lies inside the disc of
convergence.
-/

namespace Work.EQ.Fatou

open Filter MeasureTheory Complex
open scoped Interval

theorem tendsto_integral_partialSum_normSq {h : ℂ → ℂ} {a : ℕ → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ρ < R)
    (ha : ∀ z ∈ Metric.ball (0:ℂ) R, HasSum (fun n => a n * z^n) (h z)) :
    Filter.Tendsto
      (fun N => ∫ θ in (0:ℝ)..2 * Real.pi,
        ‖∑ n ∈ Finset.range N, a n * (ρ * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2)
      Filter.atTop
      (nhds (∫ θ in (0:ℝ)..2 * Real.pi, ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖^2)) := by
  -- absolute summability of the coefficients at the smaller radius
  have hsum : Summable (fun n => ‖a n‖ * ρ^n) :=
    (summable_norm_mul_pow hρ hR (fun z hz => ⟨h z, ha z hz⟩)).1
  -- the uniform bound `M = ∑ ‖aₙ‖ ρⁿ`
  set M : ℝ := ∑' n, ‖a n‖ * ρ^n with hMdef
  have hterm_nn : ∀ n, 0 ≤ ‖a n‖ * ρ^n :=
    fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le n)
  have hle_tsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, ‖a n‖ * ρ^n) ≤ M := by
    intro N
    rw [hMdef]
    exact hsum.sum_le_tsum (Finset.range N) (fun n _ => hterm_nn n)
  -- the circle point has norm `ρ`, hence lies inside the ball of radius `R`
  have hnorm_c : ∀ θ : ℝ, ‖(ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)‖ = ρ := by
    intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
  have hmem : ∀ θ : ℝ, (ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I) ∈ Metric.ball (0:ℂ) R := by
    intro θ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hnorm_c θ]
    exact hR
  -- the restricted measure `volume ↾ (0, 2π]` is finite
  have hInt : (volume : Measure ℝ) (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))) :=
    (isFiniteMeasure_restrict).2 hInt
  -- measurability of the (continuous) partial sums
  have hmeas : ∀ᶠ N : ℕ in Filter.atTop, AEStronglyMeasurable
      (fun θ : ℝ => ‖∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2)
      (volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))) :=
    Filter.Eventually.of_forall (fun N => Continuous.aestronglyMeasurable (by fun_prop))
  -- the uniform bound
  have hbound : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))),
      ‖(‖∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2 : ℝ)‖ ≤ M^2 := by
    refine Filter.Eventually.of_forall (fun N => Filter.Eventually.of_forall (fun θ => ?_))
    have hS : ‖∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖ ≤ M := by
      calc ‖∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖
          ≤ ∑ n ∈ Finset.range N,
              ‖a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖ :=
            norm_sum_le _ _
        _ = ∑ n ∈ Finset.range N, ‖a n‖ * ρ^n := by
            apply Finset.sum_congr rfl
            intro n _
            rw [norm_mul, norm_pow, hnorm_c θ]
        _ ≤ M := hle_tsum N
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hS 2
  have hint : Integrable (fun _ : ℝ => M^2) (volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))) :=
    integrable_const (M^2)
  -- pointwise convergence to `h` on the circle
  have hlim : ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))), Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.range N, a n * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2)
      Filter.atTop (nhds (‖h ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖^2)) :=
    Filter.Eventually.of_forall (fun θ =>
      (((ha _ (hmem θ)).tendsto_sum_nat).norm).pow 2)
  -- dominated convergence
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M^2) hmeas hbound hint hlim
  simp only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 2 * Real.pi by positivity)] at hDCT ⊢
  exact hDCT

end Work.EQ.Fatou
