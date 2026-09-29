import Mathlib
import Submission.Work.CPull.defs

namespace Work.CPull

open PowerSeries

/-- Coefficient of `X * f`: the shift of the coefficients of `f` with a zero in degree `0`.
This is `PowerSeries.coeff_mul_X_pow'` transported across `X * f = f * X`. -/
lemma coeff_mulX (f : PowerSeries ℚ) (n : ℕ) :
    (PowerSeries.coeff n (PowerSeries.X * f) : ℚ)
      = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  rw [mul_comm (PowerSeries.X) f, ← pow_one PowerSeries.X, PowerSeries.coeff_mul_X_pow']

/-- **Closure of `PullbackMero` under multiplication by `X`.**

If the germ at `0` of `Σₙ aₙ Ψ(z)ⁿ` is the holomorphic function `N` (`aₙ` the coefficients of `f`),
then the same is true of the shifted series `Σₙ aₙ₋₁ Ψ(z)ⁿ`, whose germ is `Ψ(z)·N(z)`; hence the
pullback of `X * f` along `Ψ` is meromorphic with denominator `1`.
This is the `n = 1` shift used to turn the auxiliary function of the paper (a `ℚ(x)`-combination of
the `fᵢ` and their derivatives) into a combination of the pullbacks `fᵢ ∘ Ψ`. -/
theorem pullbackMero_mulX {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ), HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    Submission.CDTPlan.PullbackMero (PowerSeries.X * f) Ψ := by
  -- denominator `1`, numerator `Ψ · N`
  refine ⟨1, fun z => Ψ z * N z, by simp, hΨ.mul hN, ?_⟩
  filter_upwards [hgerm] with z hz
  -- shift the convergent series by one place: multiply by `Ψ z`
  have h1 : HasSum (fun m : ℕ => ((PowerSeries.coeff m f : ℚ) : ℂ) * Ψ z ^ (m + 1))
      (Ψ z * N z) := by
    have h2 := hz.mul_left (Ψ z)
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h2
  simp only [Polynomial.eval_one, div_one]
  -- keep the finitely many vanished terms, so that the series is indexed from `0`
  set d : ℕ → ℂ := fun k =>
    if 1 ≤ k then ((PowerSeries.coeff (k - 1) f : ℚ) : ℂ) * Ψ z ^ k else 0 with hd
  have hdshift : HasSum (fun m => d (m + 1)) (Ψ z * N z) := by
    refine h1.congr_fun fun m => ?_
    simp [hd, Nat.le_add_left 1 m]
  have hdzero : d 0 = 0 := by simp [hd]
  have hdsum : HasSum d (Ψ z * N z) := by
    rw [← (hasSum_nat_add_iff' (f := d) (g := Ψ z * N z) 1)]
    rw [Finset.sum_range_one, hdzero, sub_zero]
    exact hdshift
  -- identify the summands with the coefficients of `X * f`
  refine hdsum.congr_fun fun n => ?_
  rw [coeff_mulX]
  by_cases h : 1 ≤ n <;> simp [hd, h]

end Work.CPull
