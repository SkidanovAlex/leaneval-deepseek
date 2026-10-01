import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_outer_circle_bound
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_windowSum_le_inner_divisor
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_windowSum_le_ball11
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_jensenBound_le

namespace Work.LinnikAreas.Zeta1Aux

/-- **Local zero count for `ζ₁` near a height `t`.**

Assuming every zero of `riemannZeta₁` *with non-zero imaginary part* lies in the critical
strip (`hstrip`; this is the true statement, the trivial zeros `-2, -4, …` are real), the
number of zeros of `riemannZeta₁` with `|Im - t| ≤ 3`, counted with multiplicity (the divisor
on the large ball of radius `|t| + 6`), is at most `C * log (|t| + 3)`.

Route for `|t| ≥ 5`: Jensen's inequality `AnalyticOnNhd.sum_divisor_le` (Mathlib) for
`f = riemannZeta₁` with centre `c = 2 + i t`, inner radius `37/10` and outer radius `4`:
* every zero `u` counted by the indicator has `|u.im| ≥ |t| - 3 ≥ 2 ≠ 0`, so by `hstrip`
  `Re u ∈ (0,1)`, whence `‖u - c‖ ^ 2 ≤ 4 + 9 = 13 < (37/10) ^ 2`: it lies in the inner ball
  (and `‖u‖ ≤ |t| + 4 ≤ |t| + 6`);
* `‖ζ₁ c‖ ≥ 1/4` (`zeta1_re_two_lower`);
* on the outer circle `‖w - c‖ = 4` one has `‖ζ₁ w‖ = ‖w - 1‖ * ‖ζ w‖ ≤ (|t| + 7) * C * (|t| + 9)^12`
  combining `zeta_strip_polyGrowth` (`-1 ≤ σ ≤ 3`), `zeta_strip_polyGrowth_neg`
  (`-2 ≤ σ ≤ -1`) and `zeta_norm_le_const_of_three_le_re` (`3 ≤ σ`), using `|Im w| ≥ 1`.
* the comparison of the indicator sum over `closedBall 0 (|t| + 6)` with the inner divisor sum
  uses `Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le`.
For `1 ≤ |t| ≤ 5` the sum is bounded by the (finite) total multiplicity of the zeros of `ζ₁`
in the closed ball of radius `11`, a fixed nonnegative real number `N₀`
(`Commons.NumberTheory.Zeta.zetaZeroBall` provides the finitely many zeros), and, since
`log (|t| + 3) ≥ log 4 > 1`, the same constant works there.
The case `t < 0` follows by applying the argument to `-t` (all cited bounds are symmetric
under `t ↦ -t`). -/
theorem zeta1_windowZeroCount
    (hstrip : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) ≤ C * Real.log (|t| + 3) := by
  classical
  rcases zeta1_outer_circle_bound with ⟨C1, hC1pos, hC1spec⟩
  let Cbig : ℝ := max C1 1
  have hCbig1 : (1 : ℝ) ≤ Cbig := le_max_right _ _
  let D11 : ℂ → ℤ := fun u => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) 11) u
  let N0 : ℝ := ((∑ᶠ u : ℂ, D11 u : ℤ) : ℝ)
  let Clarge : ℝ := (Real.log 4 + Real.log Cbig + 13 * Real.log 3 + 13) / Real.log (4 / (37 / 10))
  have hN0nn : 0 ≤ N0 := by
    apply Int.cast_nonneg
    apply finsum_nonneg
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁)
      (U := Metric.closedBall (0 : ℂ) 11) (fun z _ => differentiable_riemannZeta₁.analyticAt z) u
  have hClarge_nn : 0 ≤ Clarge := by
    apply div_nonneg
    · have h1 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have h2 : 0 ≤ Real.log Cbig := Real.log_nonneg hCbig1
      have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    · exact le_of_lt (Real.log_pos (by norm_num))
  refine ⟨max Clarge N0 + 1, ?_, ?_⟩
  · linarith [hClarge_nn, hN0nn, le_max_left Clarge N0, le_max_right Clarge N0]
  · intro t ht
    have hlog1 : (1 : ℝ) ≤ Real.log (|t| + 3) := by
      have h4 : Real.log 4 ≤ Real.log (|t| + 3) :=
        Real.log_le_log (by norm_num) (by nlinarith [ht])
      exact le_trans Commons.NumberTheory.Linnik.log_four_ge_one h4
    have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 3) := le_trans (by norm_num) hlog1
    by_cases h5 : 5 ≤ |t|
    · have hP2 := zeta1_windowSum_le_inner_divisor hstrip h5
      have hJ : ((∑ᶠ u : ℂ, MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ)
          ≤ Real.log (Cbig * (|t| + 9) ^ 13 / ‖riemannZeta₁ ((2 : ℂ) + Complex.I * (t : ℂ))‖)
              / Real.log (4 / (37 / 10)) := by
        set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
        set M : ℝ := Cbig * (|t| + 9) ^ 13 with hM
        have hle1 : (1 : ℝ) ≤ M := by
          rw [hM]
          have hp : (1 : ℝ) ≤ (|t| + 9) ^ 13 := one_le_pow₀ (by nlinarith [abs_nonneg t])
          nlinarith [hCbig1, hp]
        have hf_bound : ∀ z ∈ Metric.sphere c |(4 : ℝ)|, ‖riemannZeta₁ z‖ ≤ M := by
          intro z hz
          have hz' : z ∈ Metric.sphere ((2 : ℂ) + Complex.I * (t : ℂ)) 4 := by simpa [c] using hz
          have h1 := hC1spec t h5 z hz'
          rw [hM]
          have h2 : (0 : ℝ) ≤ (|t| + 9) ^ 13 := by positivity
          calc ‖riemannZeta₁ z‖ ≤ C1 * (|t| + 9) ^ 13 := h1
            _ ≤ max C1 1 * (|t| + 9) ^ 13 := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
        have h2f : riemannZeta₁ c ≠ 0 := by
          intro hz0
          have hlow := Commons.NumberTheory.Zeta.zeta1_re_two_lower t
          have hz : ‖riemannZeta₁ c‖ = 0 := by rw [hz0]; simp
          rw [hc] at hz
          rw [hz] at hlow
          norm_num at hlow
        have hJj := AnalyticOnNhd.sum_divisor_le (c := c) (r := (37 : ℝ) / 10) (R := (4 : ℝ)) (M := M)
          (f := riemannZeta₁)
          (by norm_num : 0 < |(37 : ℝ) / 10|)
          (by norm_num : |(37 : ℝ) / 10| < |(4 : ℝ)|)
          hle1
          (fun z _ => differentiable_riemannZeta₁.analyticAt z)
          h2f hf_bound
        rw [show |(37 : ℝ) / 10| = 37 / 10 by norm_num] at hJj
        simpa [M, hc] using hJj
      have hA := zeta1_jensenBound_le hCbig1 h5
      calc (∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
              (if |u.im - t| ≤ 3 then 1 else 0))
          ≤ ((∑ᶠ u : ℂ, MeromorphicOn.divisor riemannZeta₁
              (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ) := hP2
        _ ≤ Real.log (Cbig * (|t| + 9) ^ 13 / ‖riemannZeta₁ ((2 : ℂ) + Complex.I * (t : ℂ))‖)
              / Real.log (4 / (37 / 10)) := hJ
        _ ≤ Clarge * Real.log (|t| + 3) := hA
        _ ≤ (max Clarge N0 + 1) * Real.log (|t| + 3) := by
            apply mul_le_mul_of_nonneg_right _ hlog0
            linarith [le_max_left Clarge N0]
    · have hle : |t| ≤ 5 := le_of_lt (lt_of_not_ge h5)
      have hP3 := zeta1_windowSum_le_ball11 hle
      calc (∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
              (if |u.im - t| ≤ 3 then 1 else 0))
          ≤ N0 := hP3
        _ ≤ max Clarge N0 + 1 := by linarith [le_max_right Clarge N0]
        _ ≤ (max Clarge N0 + 1) * Real.log (|t| + 3) := by
            have hnn : (0 : ℝ) ≤ max Clarge N0 + 1 := by
              linarith [hClarge_nn, le_max_left Clarge N0]
            nlinarith [hnn, hlog1]

end Work.LinnikAreas.Zeta1Aux
