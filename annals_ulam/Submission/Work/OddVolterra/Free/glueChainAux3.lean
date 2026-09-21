import Mathlib
import Submission.Work.OddVolterra.Free.glueChainAux

/-!
# The degenerate (`cos α = 1`) far-region estimates

When `sin α = 0` and `4/5 ≤ cos α` we have `cos α = 1`, and the second derivative at `α` of a
composition `F ∘ cos` is controlled through the *slope* of `deriv (F ∘ cos)` rather than through the
explicit second-derivative formula (which is unavailable, since `deriv F` need not be
differentiable at `1`).
-/

namespace Work.OddVolterra.Free

open Filter
open scoped Topology

/-- On `(-1/2, 1/2) \ {0}` the sine does not vanish. -/
theorem sin_ne_zero_of_abs_lt_half_of_ne {h : ℝ} (hne : h ≠ 0) (hh : |h| < 1 / 2) :
    Real.sin h ≠ 0 := by
  intro hzero
  have hlt := abs_lt.mp hh
  have h0 : h = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [Real.pi_gt_three, hlt.1]) (by linarith [Real.pi_gt_three, hlt.2])).mp hzero
  exact hne h0

/-- Degenerate case `cos α = 1` of the second derivative of a composition with `cos`. -/
theorem abs_deriv_deriv_comp_cos_degenerate {F : ℝ → ℝ} {α M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hcos1 : Real.cos α = 1) (hsin0 : Real.sin α = 0)
    (hFd : DifferentiableAt ℝ F (Real.cos α))
    (hH0 : deriv (fun y : ℝ => F (Real.cos y)) α = 0)
    (hbd : ∀ᶠ h in 𝓝[≠] (0:ℝ), |deriv F (Real.cos h)| ≤ C * (M + (M + 1) * |h|)) :
    |deriv (deriv (fun y : ℝ => F (Real.cos y))) α| ≤ C * M := by
  rw [eventually_nhdsWithin_iff] at hbd
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hbd
  have hbd' : ∃ δ' : ℝ, 0 < δ' ∧ ∀ h : ℝ, 0 < |h| → |h| < δ' →
      |deriv (fun y : ℝ => F (Real.cos y)) (α + h) - deriv (fun y : ℝ => F (Real.cos y)) α|
        ≤ (C * M + C * (M + 1) * |h|) * |h| := by
    refine ⟨min δ (1 / 2), lt_min hδpos (by norm_num), fun h hh0 hh1 => ?_⟩
    have hhδ : |h| < δ := lt_of_lt_of_le hh1 (min_le_left _ _)
    have hhhalf : |h| < 1 / 2 := lt_of_lt_of_le hh1 (min_le_right _ _)
    have hhne : h ≠ 0 := by intro hc; rw [hc, abs_zero] at hh0; exact lt_irrefl 0 hh0
    rw [hH0, sub_zero]
    have hcosh : Real.cos (α + h) = Real.cos h := by rw [Real.cos_add, hsin0, hcos1]; ring
    have hsinh : Real.sin (α + h) = Real.sin h := by rw [Real.sin_add, hsin0, hcos1]; ring
    by_cases hDv : DifferentiableAt ℝ F (Real.cos h)
    · have hc : deriv (fun y : ℝ => F (Real.cos y)) (α + h)
          = deriv F (Real.cos (α + h)) * deriv Real.cos (α + h) :=
        deriv_comp (h₂ := F) (h := Real.cos) (x := α + h)
          (by rw [hcosh]; exact hDv) Real.differentiableAt_cos
      rw [hc, Real.deriv_cos, hcosh, hsinh]
      have h1 : |deriv F (Real.cos h)| ≤ C * (M + (M + 1) * |h|) :=
        hδ (by simpa [Real.dist_eq] using hhδ) (by simpa using hhne)
      have hs : |Real.sin h| ≤ |h| := Real.abs_sin_le_abs
      calc |deriv F (Real.cos h) * -Real.sin h| = |deriv F (Real.cos h)| * |Real.sin h| := by
            rw [abs_mul, abs_neg]
        _ ≤ (C * (M + (M + 1) * |h|)) * |h| := by gcongr
        _ = (C * M + C * (M + 1) * |h|) * |h| := by ring
    · have hnt : ¬ DifferentiableAt ℝ (fun y : ℝ => F (Real.cos y)) (α + h) :=
        not_differentiableAt_comp_cos
          (by rw [hsinh]; exact sin_ne_zero_of_abs_lt_half_of_ne hhne hhhalf)
          (by rwa [hcosh])
      rw [deriv_zero_of_not_differentiableAt hnt, abs_zero]
      have hnn : (0:ℝ) ≤ (C * M + C * (M + 1) * |h|) * |h| := by
        have h1 : (0:ℝ) ≤ C * M := mul_nonneg hC hM
        have h2 : (0:ℝ) ≤ C * (M + 1) * |h| := by positivity
        have h3 : (0:ℝ) ≤ |h| := abs_nonneg h
        nlinarith [h1, h2, h3]
      exact hnn
  exact abs_deriv_le_of_eventually_lipschitz_affine (mul_nonneg hC hM) hbd'

/-- Near `0`, the derivative of `v ↦ 2 R v / v ^ 2` at `cos h` is controlled by `M` and `|h|`. -/
theorem eventually_abs_deriv_two_mul_div_sq_le {R : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hRd : DifferentiableAt ℝ R 1) (hRd' : DifferentiableAt ℝ (deriv R) 1)
    (hRu : |R 1| ≤ M) (hRu' : |deriv R 1| ≤ M) (hRu'' : |deriv (deriv R) 1| ≤ M) :
    ∀ᶠ h in 𝓝[≠] (0:ℝ),
      |deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos h)| ≤ 40 * (M + (M + 1) * |h|) := by
  obtain ⟨δR, hδRpos, hδR⟩ := exists_bound_of_hasDerivAt (f := R) (x := (1:ℝ)) hRd.hasDerivAt
  obtain ⟨δD, hδDpos, hδD⟩ :=
    exists_bound_of_hasDerivAt (f := deriv R) (x := (1:ℝ)) hRd'.hasDerivAt
  have hδ0 : 0 < min (min δR δD) (1 / 10) := lt_min (lt_min hδRpos hδDpos) (by norm_num)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ0] with h hh hhne
  have hhδ : |h| < min (min δR δD) (1 / 10) := by simpa [Real.dist_eq] using hh
  have hhR : |h| < δR := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhD : |h| < δD := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh10 : |h| < 1 / 10 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hcosh_ge : (1:ℝ) / 2 ≤ Real.cos h := by
    have h1 : (1:ℝ) - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
    have h2 : h ^ 2 / 2 < 1 / 8 := by nlinarith [abs_lt.mp hh10]
    linarith
  have hcosh_pos : 0 < Real.cos h := by linarith
  have hcos_abs : |Real.cos h - 1| ≤ h ^ 2 / 2 := by
    have h1 : (1:ℝ) - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
    have h2 : Real.cos h ≤ 1 := Real.cos_le_one h
    have h3 : Real.cos h - 1 ≤ 0 := by linarith only [h2]
    rw [abs_of_nonpos h3]
    linarith only [h1]
  have hcos_le_h : h ^ 2 / 2 ≤ |h| := by
    have h0 : (0:ℝ) ≤ |h| := abs_nonneg h
    nlinarith [sq_abs h, sq_nonneg (|h|), h0, hh10]
  have hcos_lt : |Real.cos h - 1| < δR := by
    have h4 : h ^ 2 / 2 < δR / 2 := by nlinarith [abs_lt.mp hhR]
    linarith
  have hcos_ltD : |Real.cos h - 1| < δD := by
    have h4 : h ^ 2 / 2 < δD / 2 := by nlinarith [abs_lt.mp hhD]
    linarith
  have hR1 : |R (Real.cos h)| ≤ M + (M + 1) * |h| := by
    have h5 := hδR (Real.cos h - 1) hcos_lt
    rw [show (1:ℝ) + (Real.cos h - 1) = Real.cos h from by ring] at h5
    have h7 : |Real.cos h - 1| ≤ |h| := le_trans hcos_abs hcos_le_h
    have h8 : |deriv R 1| + 1 ≤ M + 1 := by linarith only [hRu']
    have h6 : (|deriv R 1| + 1) * |Real.cos h - 1| ≤ (M + 1) * |h| :=
      mul_le_mul h8 h7 (abs_nonneg _) (by positivity)
    have h9 : |R (Real.cos h)| ≤ |R (Real.cos h) - R 1| + |R 1| := by
      have hh := abs_add_le (R (Real.cos h) - R 1) (R 1)
      simpa using hh
    linarith only [h5, h6, h9, hRu]
  have hD1 : |deriv R (Real.cos h)| ≤ M + (M + 1) * |h| := by
    have h5 := hδD (Real.cos h - 1) hcos_ltD
    rw [show (1:ℝ) + (Real.cos h - 1) = Real.cos h from by ring] at h5
    have h7 : |Real.cos h - 1| ≤ |h| := le_trans hcos_abs hcos_le_h
    have h8 : |deriv (deriv R) 1| + 1 ≤ M + 1 := by linarith only [hRu'']
    have h6 : (|deriv (deriv R) 1| + 1) * |Real.cos h - 1| ≤ (M + 1) * |h| :=
      mul_le_mul h8 h7 (abs_nonneg _) (by positivity)
    have h9 : |deriv R (Real.cos h)| ≤ |deriv R (Real.cos h) - deriv R 1| + |deriv R 1| := by
      have hh := abs_add_le (deriv R (Real.cos h) - deriv R 1) (deriv R 1)
      simpa using hh
    linarith only [h5, h6, h9, hRu']
  by_cases hDv : DifferentiableAt ℝ R (Real.cos h)
  · rw [deriv_two_mul_div_sq R (ne_of_gt hcosh_pos) hDv]
    have h4 : (1:ℝ) / 4 ≤ Real.cos h ^ 2 := by nlinarith
    have h4' : (1:ℝ) / 8 ≤ Real.cos h ^ 3 := by nlinarith
    have hker : (0:ℝ) ≤ M + (M + 1) * |h| := by positivity
    have h4 : (1:ℝ) / 4 ≤ Real.cos h ^ 2 := by nlinarith
    have h4' : (1:ℝ) / 8 ≤ Real.cos h ^ 3 := by nlinarith
    have h1 : |2 * deriv R (Real.cos h) / Real.cos h ^ 2| ≤ 2 * (M + (M + 1) * |h|) * 4 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos h ^ 2), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hnum : 2 * |deriv R (Real.cos h)| ≤ 2 * (M + (M + 1) * |h|) := by linarith
      have hden : 1 / Real.cos h ^ 2 ≤ 1 / (1 / 4 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h4
      calc 2 * |deriv R (Real.cos h)| / Real.cos h ^ 2
          = 2 * |deriv R (Real.cos h)| * (1 / Real.cos h ^ 2) := by ring
        _ ≤ 2 * (M + (M + 1) * |h|) * (1 / (1 / 4 : ℝ)) :=
            mul_le_mul hnum hden (by positivity) (by positivity)
        _ = 2 * (M + (M + 1) * |h|) * 4 := by norm_num
    have h2 : |4 * R (Real.cos h) / Real.cos h ^ 3| ≤ 4 * (M + (M + 1) * |h|) * 8 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos h ^ 3), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4)]
      have hnum : 4 * |R (Real.cos h)| ≤ 4 * (M + (M + 1) * |h|) := by linarith
      have hden : 1 / Real.cos h ^ 3 ≤ 1 / (1 / 8 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h4'
      calc 4 * |R (Real.cos h)| / Real.cos h ^ 3
          = 4 * |R (Real.cos h)| * (1 / Real.cos h ^ 3) := by ring
        _ ≤ 4 * (M + (M + 1) * |h|) * (1 / (1 / 8 : ℝ)) :=
            mul_le_mul hnum hden (by positivity) (by positivity)
        _ = 4 * (M + (M + 1) * |h|) * 8 := by norm_num
    linarith [abs_sub_le_abs_add (2 * deriv R (Real.cos h) / Real.cos h ^ 2)
      (4 * R (Real.cos h) / Real.cos h ^ 3), h1, h2]
  · rw [deriv_zero_of_not_differentiableAt
      (not_differentiableAt_two_mul_div_sq R (ne_of_gt hcosh_pos) hDv), abs_zero]
    positivity

/-- Near `0`, the derivative of `v ↦ 2 S v / v` at `cos h` is controlled by `M` and `|h|`. -/
theorem eventually_abs_deriv_two_mul_div_le {S : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hSd : DifferentiableAt ℝ S 1) (hSd' : DifferentiableAt ℝ (deriv S) 1)
    (hSu : |S 1| ≤ M) (hSu' : |deriv S 1| ≤ M) (hSu'' : |deriv (deriv S) 1| ≤ M) :
    ∀ᶠ h in 𝓝[≠] (0:ℝ),
      |deriv (fun v : ℝ => 2 * S v / v) (Real.cos h)| ≤ 12 * (M + (M + 1) * |h|) := by
  obtain ⟨δR, hδRpos, hδR⟩ := exists_bound_of_hasDerivAt (f := S) (x := (1:ℝ)) hSd.hasDerivAt
  obtain ⟨δD, hδDpos, hδD⟩ :=
    exists_bound_of_hasDerivAt (f := deriv S) (x := (1:ℝ)) hSd'.hasDerivAt
  have hδ0 : 0 < min (min δR δD) (1 / 10) := lt_min (lt_min hδRpos hδDpos) (by norm_num)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ0] with h hh hhne
  have hhδ : |h| < min (min δR δD) (1 / 10) := by simpa [Real.dist_eq] using hh
  have hhR : |h| < δR := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhD : |h| < δD := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh10 : |h| < 1 / 10 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hcosh_ge : (1:ℝ) / 2 ≤ Real.cos h := by
    have h1 : (1:ℝ) - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
    have h2 : h ^ 2 / 2 < 1 / 8 := by nlinarith [abs_lt.mp hh10]
    linarith
  have hcosh_pos : 0 < Real.cos h := by linarith
  have hcos_abs : |Real.cos h - 1| ≤ h ^ 2 / 2 := by
    have h1 : (1:ℝ) - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
    have h2 : Real.cos h ≤ 1 := Real.cos_le_one h
    have h3 : Real.cos h - 1 ≤ 0 := by linarith only [h2]
    rw [abs_of_nonpos h3]
    linarith only [h1]
  have hcos_le_h : h ^ 2 / 2 ≤ |h| := by
    have h0 : (0:ℝ) ≤ |h| := abs_nonneg h
    nlinarith [sq_abs h, sq_nonneg (|h|), h0, hh10]
  have hcos_lt : |Real.cos h - 1| < δR := by
    have h4 : h ^ 2 / 2 < δR / 2 := by nlinarith [abs_lt.mp hhR]
    linarith
  have hcos_ltD : |Real.cos h - 1| < δD := by
    have h4 : h ^ 2 / 2 < δD / 2 := by nlinarith [abs_lt.mp hhD]
    linarith
  have hS1 : |S (Real.cos h)| ≤ M + (M + 1) * |h| := by
    have h5 := hδR (Real.cos h - 1) hcos_lt
    rw [show (1:ℝ) + (Real.cos h - 1) = Real.cos h from by ring] at h5
    have h7 : |Real.cos h - 1| ≤ |h| := le_trans hcos_abs hcos_le_h
    have h8 : |deriv S 1| + 1 ≤ M + 1 := by linarith only [hSu']
    have h6 : (|deriv S 1| + 1) * |Real.cos h - 1| ≤ (M + 1) * |h| :=
      mul_le_mul h8 h7 (abs_nonneg _) (by positivity)
    have h9 : |S (Real.cos h)| ≤ |S (Real.cos h) - S 1| + |S 1| := by
      have hh := abs_add_le (S (Real.cos h) - S 1) (S 1)
      simpa using hh
    linarith only [h5, h6, h9, hSu]
  have hD1 : |deriv S (Real.cos h)| ≤ M + (M + 1) * |h| := by
    have h5 := hδD (Real.cos h - 1) hcos_ltD
    rw [show (1:ℝ) + (Real.cos h - 1) = Real.cos h from by ring] at h5
    have h7 : |Real.cos h - 1| ≤ |h| := le_trans hcos_abs hcos_le_h
    have h8 : |deriv (deriv S) 1| + 1 ≤ M + 1 := by linarith only [hSu'']
    have h6 : (|deriv (deriv S) 1| + 1) * |Real.cos h - 1| ≤ (M + 1) * |h| :=
      mul_le_mul h8 h7 (abs_nonneg _) (by positivity)
    have h9 : |deriv S (Real.cos h)| ≤ |deriv S (Real.cos h) - deriv S 1| + |deriv S 1| := by
      have hh := abs_add_le (deriv S (Real.cos h) - deriv S 1) (deriv S 1)
      simpa using hh
    linarith only [h5, h6, h9, hSu']
  by_cases hDv : DifferentiableAt ℝ S (Real.cos h)
  · rw [deriv_two_mul_div S (ne_of_gt hcosh_pos) hDv]
    have h4 : (1:ℝ) / 4 ≤ Real.cos h ^ 2 := by nlinarith
    have h1 : |2 * deriv S (Real.cos h) / Real.cos h| ≤ 2 * (M + (M + 1) * |h|) * 2 := by
      rw [abs_div, abs_of_pos hcosh_pos, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hnum : 2 * |deriv S (Real.cos h)| ≤ 2 * (M + (M + 1) * |h|) := by linarith
      have hden : 1 / Real.cos h ≤ 1 / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hcosh_ge
      calc 2 * |deriv S (Real.cos h)| / Real.cos h
          = 2 * |deriv S (Real.cos h)| * (1 / Real.cos h) := by ring
        _ ≤ 2 * (M + (M + 1) * |h|) * (1 / (1 / 2 : ℝ)) :=
            mul_le_mul hnum hden (by positivity) (by positivity)
        _ = 2 * (M + (M + 1) * |h|) * 2 := by norm_num
    have h2 : |2 * S (Real.cos h) / Real.cos h ^ 2| ≤ 2 * (M + (M + 1) * |h|) * 4 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos h ^ 2), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hnum : 2 * |S (Real.cos h)| ≤ 2 * (M + (M + 1) * |h|) := by linarith
      have hden : 1 / Real.cos h ^ 2 ≤ 1 / (1 / 4 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h4
      calc 2 * |S (Real.cos h)| / Real.cos h ^ 2
          = 2 * |S (Real.cos h)| * (1 / Real.cos h ^ 2) := by ring
        _ ≤ 2 * (M + (M + 1) * |h|) * (1 / (1 / 4 : ℝ)) :=
            mul_le_mul hnum hden (by positivity) (by positivity)
        _ = 2 * (M + (M + 1) * |h|) * 4 := by norm_num
    linarith [abs_sub_le_abs_add (2 * deriv S (Real.cos h) / Real.cos h)
      (2 * S (Real.cos h) / Real.cos h ^ 2), h1, h2]
  · rw [deriv_zero_of_not_differentiableAt
      (not_differentiableAt_two_mul_div S (ne_of_gt hcosh_pos) hDv), abs_zero]
    positivity

end Work.OddVolterra.Free
