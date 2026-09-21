import Mathlib
import Submission.Work.OddVolterra.Free.glueChainAux

/-!
# Second-derivative estimates for the glue functions

Estimates for the junk-value aware second derivative at a point `u ≥ 4/5` of the two functions
`v ↦ 2 * R v / v ^ 2` and `v ↦ 2 * R v / v`, from pointwise bounds on `R`, `deriv R` and
`deriv (deriv R)` at `u`.

If `R` is differentiable on a neighbourhood of `u` the functions agree near `u` with their
explicit quotient-rule expressions and the classical second-derivative formula gives the bound.
Otherwise `R` fails to be differentiable at points accumulating at `u`; then the first derivative
of the quotient vanishes at those points, and since it is differentiable at `u` by hypothesis its
value and its derivative at `u` both vanish (or it is a junk value, which is `0`).
-/

namespace Work.OddVolterra.Free

open Filter
open scoped Topology

/-- Estimate for `deriv (deriv (v ↦ 2 R v / v^2)) u`. -/
theorem deriv_deriv_two_mul_div_sq_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {R : ℝ → ℝ} {u M : ℝ},
      0 ≤ M →
      4 / 5 ≤ u →
      DifferentiableAt ℝ R u →
      DifferentiableAt ℝ (deriv R) u →
      |R u| ≤ M →
      |deriv R u| ≤ M →
      |deriv (deriv R) u| ≤ M →
      |deriv (deriv (fun v : ℝ => 2 * R v / v ^ 2)) u| ≤ K * M := by
  refine ⟨100, by norm_num, ?_⟩
  intro R u M hM hu hRd hDd h0 h1 h2
  have hupos : 0 < u := by linarith
  have hI2 : 1 / u ^ 2 ≤ 25 / 16 := by
    have hp : ((4:ℝ) / 5) ^ 2 ≤ u ^ 2 := by gcongr
    calc 1 / u ^ 2 ≤ 1 / (((4:ℝ) / 5) ^ 2) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 25 / 16 := by norm_num
  have hI3 : 1 / u ^ 3 ≤ 125 / 64 := by
    have hp : ((4:ℝ) / 5) ^ 3 ≤ u ^ 3 := by gcongr
    calc 1 / u ^ 3 ≤ 1 / (((4:ℝ) / 5) ^ 3) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 125 / 64 := by norm_num
  have hI4 : 1 / u ^ 4 ≤ 625 / 256 := by
    have hp : ((4:ℝ) / 5) ^ 4 ≤ u ^ 4 := by gcongr
    calc 1 / u ^ 4 ≤ 1 / (((4:ℝ) / 5) ^ 4) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 625 / 256 := by norm_num
  by_cases hA : ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, |v - u| < δ → DifferentiableAt ℝ R v
  · obtain ⟨δ, hδ, hAd⟩ := hA
    have hev : deriv (fun v : ℝ => 2 * R v / v ^ 2) =ᶠ[𝓝 u]
        (fun v : ℝ => 2 * deriv R v / v ^ 2 - 4 * R v / v ^ 3) := by
      filter_upwards [Metric.ball_mem_nhds u (lt_min hδ (by linarith : (0:ℝ) < u / 2))] with v hv
      have hv' : |v - u| < min δ (u / 2) := by simpa [Real.dist_eq] using hv
      have hvδ : |v - u| < δ := lt_of_lt_of_le hv' (min_le_left _ _)
      have hv0 : v ≠ 0 := by
        have h := abs_lt.mp (lt_of_lt_of_le hv' (min_le_right _ _))
        linarith [h.1]
      exact deriv_two_mul_div_sq R hv0 (hAd v hvδ)
    rw [hev.deriv_eq]
    have hd1 : HasDerivAt (fun v : ℝ => 2 * deriv R v / v ^ 2)
        ((2 * deriv (deriv R) u * u ^ 2 - 2 * deriv R u * (2 * u)) / (u ^ 2) ^ 2) u := by
      have hnum : HasDerivAt (fun v : ℝ => 2 * deriv R v) (2 * deriv (deriv R) u) u :=
        hDd.hasDerivAt.const_mul 2
      have hden : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
        simpa using hasDerivAt_pow 2 u
      exact hnum.div hden (by positivity)
    have hd2 : HasDerivAt (fun v : ℝ => 4 * R v / v ^ 3)
        ((4 * deriv R u * u ^ 3 - 4 * R u * (3 * u ^ 2)) / (u ^ 3) ^ 2) u := by
      have hnum : HasDerivAt (fun v : ℝ => 4 * R v) (4 * deriv R u) u :=
        hRd.hasDerivAt.const_mul 4
      have hden : HasDerivAt (fun v : ℝ => v ^ 3) (3 * u ^ 2) u := by
        simpa using hasDerivAt_pow 3 u
      exact hnum.div hden (by positivity)
    have hsub : HasDerivAt (fun v : ℝ => 2 * deriv R v / v ^ 2 - 4 * R v / v ^ 3)
        ((2 * deriv (deriv R) u * u ^ 2 - 2 * deriv R u * (2 * u)) / (u ^ 2) ^ 2
          - (4 * deriv R u * u ^ 3 - 4 * R u * (3 * u ^ 2)) / (u ^ 3) ^ 2) u := by
      have h := hd1.sub hd2
      have hfun : ((fun v : ℝ => 2 * deriv R v / v ^ 2) - fun v : ℝ => 4 * R v / v ^ 3)
          = fun v : ℝ => 2 * deriv R v / v ^ 2 - 4 * R v / v ^ 3 := by
        funext y; rfl
      rwa [hfun] at h
    have hval : (2 * deriv (deriv R) u * u ^ 2 - 2 * deriv R u * (2 * u)) / (u ^ 2) ^ 2
          - (4 * deriv R u * u ^ 3 - 4 * R u * (3 * u ^ 2)) / (u ^ 3) ^ 2
        = 2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3 + 12 * R u / u ^ 4 := by
      field_simp
      ring
    rw [HasDerivAt.deriv hsub, hval]
    have hterm1 : |2 * deriv (deriv R) u / u ^ 2| ≤ 2 * M * (25 / 16) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < u ^ 2), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc 2 * |deriv (deriv R) u| / u ^ 2 = 2 * |deriv (deriv R) u| * (1 / u ^ 2) := by ring
        _ ≤ 2 * M * (1 / u ^ 2) := by gcongr
        _ ≤ 2 * M * (25 / 16) := by gcongr
    have hterm2 : |8 * deriv R u / u ^ 3| ≤ 8 * M * (125 / 64) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < u ^ 3), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 8)]
      calc 8 * |deriv R u| / u ^ 3 = 8 * |deriv R u| * (1 / u ^ 3) := by ring
        _ ≤ 8 * M * (1 / u ^ 3) := by gcongr
        _ ≤ 8 * M * (125 / 64) := by gcongr
    have hterm3 : |12 * R u / u ^ 4| ≤ 12 * M * (625 / 256) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < u ^ 4), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 12)]
      calc 12 * |R u| / u ^ 4 = 12 * |R u| * (1 / u ^ 4) := by ring
        _ ≤ 12 * M * (1 / u ^ 4) := by gcongr
        _ ≤ 12 * M * (625 / 256) := by gcongr
    have htri : |2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3 + 12 * R u / u ^ 4|
        ≤ |2 * deriv (deriv R) u / u ^ 2| + |8 * deriv R u / u ^ 3| + |12 * R u / u ^ 4| := by
      have h1' : |2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3|
          ≤ |2 * deriv (deriv R) u / u ^ 2| + |8 * deriv R u / u ^ 3| := by
        calc |2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3|
            = |2 * deriv (deriv R) u / u ^ 2 + -(8 * deriv R u / u ^ 3)| := by ring_nf
          _ ≤ |2 * deriv (deriv R) u / u ^ 2| + |-(8 * deriv R u / u ^ 3)| :=
              abs_add_le _ _
          _ = |2 * deriv (deriv R) u / u ^ 2| + |8 * deriv R u / u ^ 3| := by rw [abs_neg]
      have h2' : |(2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3) + 12 * R u / u ^ 4|
          ≤ |2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3| + |12 * R u / u ^ 4| :=
        abs_add_le _ _
      linarith
    calc |2 * deriv (deriv R) u / u ^ 2 - 8 * deriv R u / u ^ 3 + 12 * R u / u ^ 4|
        ≤ |2 * deriv (deriv R) u / u ^ 2| + |8 * deriv R u / u ^ 3| + |12 * R u / u ^ 4| := htri
      _ ≤ 100 * M := by nlinarith [hterm1, hterm2, hterm3, hM]
  · -- case B: `R` is not differentiable on any neighbourhood of `u`
    push Not at hA
    by_cases hD : DifferentiableAt ℝ (deriv (fun v : ℝ => 2 * R v / v ^ 2)) u
    · have hz2 : deriv (fun v : ℝ => 2 * R v / v ^ 2) u = 0 ∧
          deriv (deriv (fun v : ℝ => 2 * R v / v ^ 2)) u = 0 := by
        refine deriv_eq_zero_of_frequently_zero hD ?_
        intro δ hδ
        obtain ⟨v, hv, hvd⟩ := hA (min δ (u / 2)) (lt_min hδ (by linarith))
        have hvδ : |v - u| < δ := lt_of_lt_of_le hv (min_le_left _ _)
        have hv0 : v ≠ 0 := by
          have h := abs_lt.mp (lt_of_lt_of_le hv (min_le_right _ _))
          linarith [h.1]
        exact ⟨v, hvδ, (fun hvu => hvd (hvu.symm ▸ hRd)),
          deriv_zero_of_not_differentiableAt (not_differentiableAt_two_mul_div_sq R hv0 hvd)⟩
      rw [hz2.2, abs_zero]
      exact mul_nonneg (by norm_num) hM
    · rw [deriv_zero_of_not_differentiableAt hD, abs_zero]
      exact mul_nonneg (by norm_num) hM

/-- Estimate for `deriv (deriv (v ↦ 2 R v / v)) u`. -/
theorem deriv_deriv_two_mul_div_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {R : ℝ → ℝ} {u M : ℝ},
      0 ≤ M →
      4 / 5 ≤ u →
      DifferentiableAt ℝ R u →
      DifferentiableAt ℝ (deriv R) u →
      |R u| ≤ M →
      |deriv R u| ≤ M →
      |deriv (deriv R) u| ≤ M →
      |deriv (deriv (fun v : ℝ => 2 * R v / v)) u| ≤ K * M := by
  refine ⟨100, by norm_num, ?_⟩
  intro R u M hM hu hRd hDd h0 h1 h2
  have hupos : 0 < u := by linarith
  have hI1 : 1 / u ≤ 5 / 4 := by
    calc 1 / u ≤ 1 / ((4:ℝ) / 5) := one_div_le_one_div_of_le (by norm_num) hu
      _ = 5 / 4 := by norm_num
  have hI2 : 1 / u ^ 2 ≤ 25 / 16 := by
    have hp : ((4:ℝ) / 5) ^ 2 ≤ u ^ 2 := by gcongr
    calc 1 / u ^ 2 ≤ 1 / (((4:ℝ) / 5) ^ 2) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 25 / 16 := by norm_num
  have hI3 : 1 / u ^ 3 ≤ 125 / 64 := by
    have hp : ((4:ℝ) / 5) ^ 3 ≤ u ^ 3 := by gcongr
    calc 1 / u ^ 3 ≤ 1 / (((4:ℝ) / 5) ^ 3) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 125 / 64 := by norm_num
  by_cases hA : ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, |v - u| < δ → DifferentiableAt ℝ R v
  · obtain ⟨δ, hδ, hAd⟩ := hA
    have hev : deriv (fun v : ℝ => 2 * R v / v) =ᶠ[𝓝 u]
        (fun v : ℝ => 2 * deriv R v / v - 2 * R v / v ^ 2) := by
      filter_upwards [Metric.ball_mem_nhds u (lt_min hδ (by linarith : (0:ℝ) < u / 2))] with v hv
      have hv' : |v - u| < min δ (u / 2) := by simpa [Real.dist_eq] using hv
      have hvδ : |v - u| < δ := lt_of_lt_of_le hv' (min_le_left _ _)
      have hv0 : v ≠ 0 := by
        have h := abs_lt.mp (lt_of_lt_of_le hv' (min_le_right _ _))
        linarith [h.1]
      exact deriv_two_mul_div R hv0 (hAd v hvδ)
    rw [hev.deriv_eq]
    have hd1 : HasDerivAt (fun v : ℝ => 2 * deriv R v / v)
        ((2 * deriv (deriv R) u * u - 2 * deriv R u * 1) / u ^ 2) u := by
      have hnum : HasDerivAt (fun v : ℝ => 2 * deriv R v) (2 * deriv (deriv R) u) u :=
        hDd.hasDerivAt.const_mul 2
      have hden : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id u
      exact hnum.div hden (by positivity)
    have hd2 : HasDerivAt (fun v : ℝ => 2 * R v / v ^ 2)
        ((2 * deriv R u * u ^ 2 - 2 * R u * (2 * u)) / (u ^ 2) ^ 2) u := by
      have hnum : HasDerivAt (fun v : ℝ => 2 * R v) (2 * deriv R u) u :=
        hRd.hasDerivAt.const_mul 2
      have hden : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
        simpa using hasDerivAt_pow 2 u
      exact hnum.div hden (by positivity)
    have hsub : HasDerivAt (fun v : ℝ => 2 * deriv R v / v - 2 * R v / v ^ 2)
        ((2 * deriv (deriv R) u * u - 2 * deriv R u * 1) / u ^ 2
          - (2 * deriv R u * u ^ 2 - 2 * R u * (2 * u)) / (u ^ 2) ^ 2) u := by
      have h := hd1.sub hd2
      have hfun : ((fun v : ℝ => 2 * deriv R v / v) - fun v : ℝ => 2 * R v / v ^ 2)
          = fun v : ℝ => 2 * deriv R v / v - 2 * R v / v ^ 2 := by
        funext y; rfl
      rwa [hfun] at h
    have hval : (2 * deriv (deriv R) u * u - 2 * deriv R u * 1) / u ^ 2
          - (2 * deriv R u * u ^ 2 - 2 * R u * (2 * u)) / (u ^ 2) ^ 2
        = 2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2 + 4 * R u / u ^ 3 := by
      field_simp
      ring
    rw [HasDerivAt.deriv hsub, hval]
    have hterm1 : |2 * deriv (deriv R) u / u| ≤ 2 * M * (5 / 4) := by
      rw [abs_div, abs_of_pos hupos, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc 2 * |deriv (deriv R) u| / u = 2 * |deriv (deriv R) u| * (1 / u) := by ring
        _ ≤ 2 * M * (1 / u) := by gcongr
        _ ≤ 2 * M * (5 / 4) := by gcongr
    have hterm2 : |4 * deriv R u / u ^ 2| ≤ 4 * M * (25 / 16) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < u ^ 2), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4)]
      calc 4 * |deriv R u| / u ^ 2 = 4 * |deriv R u| * (1 / u ^ 2) := by ring
        _ ≤ 4 * M * (1 / u ^ 2) := by gcongr
        _ ≤ 4 * M * (25 / 16) := by gcongr
    have hterm3 : |4 * R u / u ^ 3| ≤ 4 * M * (125 / 64) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < u ^ 3), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4)]
      calc 4 * |R u| / u ^ 3 = 4 * |R u| * (1 / u ^ 3) := by ring
        _ ≤ 4 * M * (1 / u ^ 3) := by gcongr
        _ ≤ 4 * M * (125 / 64) := by gcongr
    have htri : |2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2 + 4 * R u / u ^ 3|
        ≤ |2 * deriv (deriv R) u / u| + |4 * deriv R u / u ^ 2| + |4 * R u / u ^ 3| := by
      have h1' : |2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2|
          ≤ |2 * deriv (deriv R) u / u| + |4 * deriv R u / u ^ 2| := by
        calc |2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2|
            = |2 * deriv (deriv R) u / u + -(4 * deriv R u / u ^ 2)| := by ring_nf
          _ ≤ |2 * deriv (deriv R) u / u| + |-(4 * deriv R u / u ^ 2)| := abs_add_le _ _
          _ = |2 * deriv (deriv R) u / u| + |4 * deriv R u / u ^ 2| := by rw [abs_neg]
      have h2' : |(2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2) + 4 * R u / u ^ 3|
          ≤ |2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2| + |4 * R u / u ^ 3| :=
        abs_add_le _ _
      linarith
    calc |2 * deriv (deriv R) u / u - 4 * deriv R u / u ^ 2 + 4 * R u / u ^ 3|
        ≤ |2 * deriv (deriv R) u / u| + |4 * deriv R u / u ^ 2| + |4 * R u / u ^ 3| := htri
      _ ≤ 100 * M := by nlinarith [hterm1, hterm2, hterm3, hM]
  · -- case B
    push Not at hA
    by_cases hD : DifferentiableAt ℝ (deriv (fun v : ℝ => 2 * R v / v)) u
    · have hz2 : deriv (fun v : ℝ => 2 * R v / v) u = 0 ∧
          deriv (deriv (fun v : ℝ => 2 * R v / v)) u = 0 := by
        refine deriv_eq_zero_of_frequently_zero hD ?_
        intro δ hδ
        obtain ⟨v, hv, hvd⟩ := hA (min δ (u / 2)) (lt_min hδ (by linarith))
        have hvδ : |v - u| < δ := lt_of_lt_of_le hv (min_le_left _ _)
        have hv0 : v ≠ 0 := by
          have h := abs_lt.mp (lt_of_lt_of_le hv (min_le_right _ _))
          linarith [h.1]
        exact ⟨v, hvδ, (fun hvu => hvd (hvu.symm ▸ hRd)),
          deriv_zero_of_not_differentiableAt (not_differentiableAt_two_mul_div R hv0 hvd)⟩
      rw [hz2.2, abs_zero]
      exact mul_nonneg (by norm_num) hM
    · rw [deriv_zero_of_not_differentiableAt hD, abs_zero]
      exact mul_nonneg (by norm_num) hM

end Work.OddVolterra.Free
