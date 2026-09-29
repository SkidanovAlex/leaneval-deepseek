import Mathlib
import Submission.Work.Holonomy3.defs

/-!
# Coefficient growth of `f` from the meromorphy of the pullback `f ∘ φ`

This file proves `Work.Holonomy3.pullback_coeff_growth`: if the pullback germ
`Σ aₙ φ(z)ⁿ` of a rational-coefficient series `f = Σ aₙ xⁿ` continues meromorphically across a
neighbourhood of `0` (`Submission.CDTPlan.PullbackMero f φ`) and `φ'(0) ≠ 0`, then the coefficients
`aₙ` grow at most geometrically.

*Mathematics.*  `PullbackMero` gives a *disk* `ball 0 r` around `0` on which
`Σ aₙ φ(z)ⁿ = N z / P(z)` converges, with `P(0) ≠ 0`.  If `φ` vanished identically on that disk,
then `φ =ᶠ[𝓝 0] 0`, hence `deriv φ 0 = 0`, contrary to `‖deriv φ 0‖ > 0`; so there is `z ∈ ball 0 r`
with `φ z ≠ 0`.  At this `z` the series `Σ aₙ wⁿ` converges for the *nonzero* number `w = φ z`;
writing `S = Σ aₙ wⁿ` (summable), the terms `aₙ wⁿ` are bounded, say `‖aₙ wⁿ‖ ≤ M`, whence
`‖aₙ‖ ≤ M·(‖w‖⁻¹)ⁿ`.  There is no need for Cauchy–Hadamard: boundedness of the terms of a
convergent series already gives the geometric bound, with `A = max 1 ‖w‖⁻¹ ≥ 1` and
`C = max 1 M > 0`.

This is exactly the "`hgr`" input of the box principle in the elementary holonomy bound
(see `Submission/Work/Holonomy3/holonomy_bound_l2.lean`, `Work.Holonomy3.siegel`).
-/

namespace Work.Holonomy3

open Filter

theorem pullback_coeff_growth {f : PowerSeries ℚ} {φ : ℂ → ℂ}
    (h : Submission.CDTPlan.PullbackMero f φ) (hφ : 0 < ‖deriv φ 0‖) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C * A ^ n := by
  classical
  obtain ⟨P, N, _hP0, _hN, hsum⟩ := h
  rw [Filter.eventually_iff] at hsum
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hsum
  -- `φ` does not vanish on a whole neighbourhood of `0`
  have hne : ∃ z ∈ Metric.ball (0 : ℂ) r, φ z ≠ 0 := by
    by_contra hc
    have hc' : ∀ z ∈ Metric.ball (0 : ℂ) r, φ z = 0 := by
      intro z hz
      by_contra hz'
      exact hc ⟨z, hz, hz'⟩
    have hev : φ =ᶠ[nhds (0 : ℂ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
      exact hc' z hz
    have hz0 : deriv φ 0 = 0 := by
      rw [hev.deriv_eq, deriv_const]
    rw [hz0, norm_zero] at hφ
    exact lt_irrefl 0 hφ
  obtain ⟨z, hzball, hzφ⟩ := hne
  -- the pullback series converges at the nonzero value `φ z`
  have hS : Summable (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * φ z ^ n) :=
    (hrsub hzball).summable
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ‖((PowerSeries.coeff n f : ℚ) : ℂ) * φ z ^ n‖ < 1 := by
    rw [← Filter.eventually_atTop]
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using
      (hS.tendsto_atTop_zero.eventually (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one))
  have hwn : 0 < ‖φ z‖ := norm_pos_iff.mpr hzφ
  set A : ℝ := max 1 ‖φ z‖⁻¹ with hA
  set C : ℝ := (∑ m ∈ Finset.range N₀, ‖((PowerSeries.coeff m f : ℚ) : ℂ)‖) + 1 with hC
  have hA1 : 1 ≤ A := by rw [hA]; exact le_max_left _ _
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hCpos : 0 < C := by rw [hC]; positivity
  have hC1 : 1 ≤ C := by
    have hs : 0 ≤ ∑ m ∈ Finset.range N₀, ‖((PowerSeries.coeff m f : ℚ) : ℂ)‖ :=
      Finset.sum_nonneg (fun m _ => norm_nonneg _)
    rw [hC]; linarith
  refine ⟨C, A, hCpos, hA1, fun n => ?_⟩
  rcases lt_or_ge n N₀ with hn | hn
  · -- finitely many initial coefficients are absorbed into `C`
    have h1 : ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤
        ∑ m ∈ Finset.range N₀, ‖((PowerSeries.coeff m f : ℚ) : ℂ)‖ :=
      Finset.single_le_sum (f := fun m => ‖((PowerSeries.coeff m f : ℚ) : ℂ)‖)
        (fun m _ => norm_nonneg _) (Finset.mem_range.mpr hn)
    calc ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖
        ≤ ∑ m ∈ Finset.range N₀, ‖((PowerSeries.coeff m f : ℚ) : ℂ)‖ := h1
      _ ≤ (∑ m ∈ Finset.range N₀, ‖((PowerSeries.coeff m f : ℚ) : ℂ)‖) + 1 := by linarith
      _ = C * 1 := by rw [hC, mul_one]
      _ ≤ C * A ^ n := mul_le_mul_of_nonneg_left (one_le_pow₀ hA1) hCpos.le
  · -- for `n ≥ N₀` the terms are `< 1`, i.e. `‖aₙ‖ < ‖φ z‖^{-n}`
    have hmul : ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ * ‖φ z‖ ^ n < 1 := by
      simpa [norm_mul, norm_pow] using hN₀ n hn
    have hbound : ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ < (‖φ z‖⁻¹) ^ n := by
      have hp : (0 : ℝ) < ‖φ z‖ ^ n := pow_pos hwn n
      rw [inv_pow, ← one_div]
      rw [lt_div_iff₀ hp]
      exact hmul
    have hstep : ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ A ^ n := le_of_lt (calc
      ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ < (‖φ z‖⁻¹) ^ n := hbound
      _ ≤ (max 1 ‖φ z‖⁻¹) ^ n := pow_le_pow_left₀ (by positivity) (le_max_right _ _) n
      _ = A ^ n := by rw [hA])
    calc ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ A ^ n := hstep
      _ = 1 * A ^ n := (one_mul _).symm
      _ ≤ C * A ^ n := mul_le_mul_of_nonneg_right hC1 (pow_nonneg hA0 n)

end Work.Holonomy3
