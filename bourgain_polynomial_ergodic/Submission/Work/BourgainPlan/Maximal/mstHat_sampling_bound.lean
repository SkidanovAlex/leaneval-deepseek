import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.lattice_shift_inv_sq_bound

namespace Work.BourgainPlan.Maximal

open scoped BigOperators

noncomputable section

/-- **Pointwise majorant for the shifted lattice sampling bound.**

Let `X ≥ 0` be a size that is bounded by `M` everywhere and by `E c²/u²` off `u = 0`.
When `c ≥ 1` the single factor `2 (M+E) c / (u² + c²)` dominates `c⁻¹ X`: on the region
`|u| ≤ c` the denominator is at most `2c²`, while off it `u² > c²` makes
`2 (M+E) c/(u²+c²) > (M+E) c/u² ≥ E c / u²`. -/
lemma mstHat_sampling_majorant {M E c u X : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E) (hc : 1 ≤ c)
    (hXa : X ≤ M) (hXb : u ≠ 0 → X ≤ E * c ^ 2 / u ^ 2) :
    c⁻¹ * X ≤ 2 * (M + E) * c / (u ^ 2 + c ^ 2) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hME : (0:ℝ) ≤ M + E := by linarith
  by_cases hle : |u| ≤ c
  · have hu2le : u ^ 2 ≤ c ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg u) hle 2
      rwa [sq_abs] at h
    have hden : c ^ 2 + u ^ 2 ≤ 2 * c ^ 2 := by linarith
    have h1 : c⁻¹ * X ≤ c⁻¹ * M := mul_le_mul_of_nonneg_left hXa (by positivity)
    have h2 : (M + E) / c ≤ 2 * (M + E) * c / (u ^ 2 + c ^ 2) := by
      rw [div_le_div_iff₀ hcpos (by positivity)]
      have hA : (M + E) * (c ^ 2 + u ^ 2) ≤ (M + E) * (2 * c ^ 2) :=
        mul_le_mul_of_nonneg_left hden hME
      nlinarith [hA]
    have h3 : c⁻¹ * M ≤ (M + E) / c := by
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hcpos)
    linarith
  · have hlt : c < |u| := not_le.mp hle
    have hu_ne : u ≠ 0 := by
      intro h; rw [h, abs_zero] at hlt; linarith
    have hu2lt : c ^ 2 < u ^ 2 := by
      have h := pow_lt_pow_left₀ hlt (le_of_lt hcpos) (by norm_num : (2:ℕ) ≠ 0)
      rwa [sq_abs] at h
    have hden : c ^ 2 + u ^ 2 < 2 * u ^ 2 := by linarith
    have h1 : c⁻¹ * X ≤ c⁻¹ * (E * c ^ 2 / u ^ 2) :=
      mul_le_mul_of_nonneg_left (hXb hu_ne) (by positivity)
    have h2 : c⁻¹ * (E * c ^ 2 / u ^ 2) = E * c / u ^ 2 := by
      field_simp
    have h3 : E * c / u ^ 2 ≤ 2 * (M + E) * c / (u ^ 2 + c ^ 2) := by
      have hu2pos : 0 < u ^ 2 := by positivity
      rw [div_le_div_iff₀ hu2pos (by positivity)]
      have hA : E * c * (c ^ 2 + u ^ 2) ≤ E * c * (2 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hden.le (mul_nonneg hE (le_of_lt hcpos))
      have hB : E * c * (2 * u ^ 2) ≤ 2 * (M + E) * c * u ^ 2 := by
        have hEM : E ≤ M + E := le_add_of_nonneg_left hM
        have h := mul_le_mul_of_nonneg_right hEM (by positivity : (0:ℝ) ≤ 2 * c * u ^ 2)
        nlinarith [h]
      linarith
    linarith

/-- **The uniform shifted-lattice sampling bound for `mstHat`.**

For a function whose period-`1` Fourier transform `mstHat η t = ∫_{−1/2}^{1/2} η u e^{−2πi t u} du`
is bounded by `M` and decays quadratically with constant `E`, the shifted dilate lattice sum
`Σ_m c⁻¹ ‖mstHat η ((m+σ)/c)‖` is bounded by a constant depending only on `M` and `E` — uniformly in
the dilation `c ≥ 1` and in the shift `σ : ℝ`.  Concretely the sum is `≤ 3M + 4E`, so `K := 3M+4E+1`
works.  Route: the terms with `|m+σ| ≤ c` number at most `2c+1 ≤ 3c` and each is `≤ M/c`; each tail
is bounded by the monotone comparison `Σ_{k≥0} 1/(w+k)² ≤ 1/w² + ∫_w^∞ dy/y² ≤ 2/w` with `w > c`,
so each tail contributes at most `2E`.  Summability follows from the finite-sum bound
(`summable_of_sum_le`), and the `tsum` bound from `Real.tsum_le_of_sum_le`. -/
theorem mstHat_sampling_bound {η : ℝ → ℂ} {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hbound : ∀ t : ℝ, ‖mstHat η t‖ ≤ M)
    (hdecay : ∀ t : ℝ, t ≠ 0 → ‖mstHat η t‖ ≤ E / t ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c σ : ℝ), 1 ≤ c →
      Summable (fun m : ℤ => c⁻¹ * ‖mstHat η ((m + σ) / c)‖) ∧
        (∑' m : ℤ, c⁻¹ * ‖mstHat η ((m + σ) / c)‖) ≤ K := by
  obtain ⟨C, hCpos, hCbound⟩ := lattice_shift_inv_sq_bound
  refine ⟨2 * C * (M + E) + 1, by positivity, ?_⟩
  intro c σ hc
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- Pointwise domination by a single shift-invariant majorant.
  have hdom : ∀ m : ℤ, c⁻¹ * ‖mstHat η ((m + σ) / c)‖ ≤
      2 * (M + E) * c / (((m : ℝ) + σ) ^ 2 + c ^ 2) := by
    intro m
    refine mstHat_sampling_majorant (M := M) (E := E) (c := c) (u := (m : ℝ) + σ)
      (X := ‖mstHat η (((m : ℝ) + σ) / c)‖) hM hE hc (hbound _) ?_
    intro hu
    have hdec := hdecay (((m : ℝ) + σ) / c) (div_ne_zero hu hcne)
    calc ‖mstHat η (((m : ℝ) + σ) / c)‖ ≤ E / (((m : ℝ) + σ) / c) ^ 2 := hdec
      _ = E * c ^ 2 / ((m : ℝ) + σ) ^ 2 := by field_simp
  have hmaj : Summable (fun m : ℤ => 2 * (M + E) * c / (((m : ℝ) + σ) ^ 2 + c ^ 2)) := by
    refine ((hCbound c hc σ).1.mul_left (2 * (M + E) * c)).congr (fun m => ?_)
    rw [one_div, div_eq_mul_inv]
  have hFsum : Summable (fun m : ℤ => c⁻¹ * ‖mstHat η ((m + σ) / c)‖) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hdom hmaj
  refine ⟨hFsum, ?_⟩
  calc ∑' m : ℤ, c⁻¹ * ‖mstHat η ((m + σ) / c)‖
      ≤ ∑' m : ℤ, 2 * (M + E) * c / (((m : ℝ) + σ) ^ 2 + c ^ 2) :=
        Summable.tsum_le_tsum hdom hFsum hmaj
    _ = 2 * (M + E) * c * (∑' m : ℤ, 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2)) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro m
        rw [one_div, div_eq_mul_inv]
    _ ≤ 2 * (M + E) * c * (C / c) := by
        apply mul_le_mul_of_nonneg_left (hCbound c hc σ).2
        positivity
    _ = 2 * C * (M + E) := by field_simp
    _ ≤ 2 * C * (M + E) + 1 := by linarith

end

end Work.BourgainPlan.Maximal
