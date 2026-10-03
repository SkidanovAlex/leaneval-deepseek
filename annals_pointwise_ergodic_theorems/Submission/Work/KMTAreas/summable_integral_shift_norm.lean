import Mathlib
import Submission.Work.KMTAreas.schwartz_decay_bound

namespace Work.KMTAreas

/-- The series `∑_k 4 * (1 + |k|)⁻²` over `ℤ` converges.  This is the majorant for the
shifted integrals of a Schwartz function; it is proved here by comparison with the
`p`-series `∑_k 1/k²` over `ℤ` (`Real.summable_one_div_int_pow`). -/
theorem summable_four_inv_shift_sq :
    Summable (fun k : ℤ => (4 : ℝ) * ((1 + |(k : ℝ)|) ^ 2)⁻¹) := by
  have hg : Summable (fun k : ℤ => (4 : ℝ) * (1 / (k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num : (1 : ℕ) < 2) |>.mul_left 4
  refine Summable.of_norm_bounded_eventually (g := fun k : ℤ => (4 : ℝ) * (1 / (k : ℝ) ^ 2))
    hg ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
  have hle : |(k : ℝ)| ^ 2 ≤ (1 + |(k : ℝ)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
  have h1 : ((1 + |(k : ℝ)|) ^ 2)⁻¹ ≤ ((k : ℝ) ^ 2)⁻¹ := by
    rw [← sq_abs (k : ℝ)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hle
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (4 : ℝ) * ((1 + |(k : ℝ)|) ^ 2)⁻¹ ≤ 4 * ((k : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 4 * (1 / (k : ℝ) ^ 2) := by rw [one_div]

theorem summable_integral_shift_norm (φ : SchwartzMap ℝ ℂ) :
    Summable (fun k : ℤ => ∫ a in Set.Ioc (0:ℝ) 1, ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖) := by
  obtain ⟨C, hCnn, hdec⟩ := schwartz_decay_bound φ
  -- For `a ∈ (0,1]` the shifted argument `a + k` is at least `|k|/2` away from `0`.
  have hshift : ∀ (k : ℤ) (a : ℝ), a ∈ Set.Ioc (0:ℝ) 1 →
      (1 + |(k:ℝ)|) / 2 ≤ 1 + |a + (k:ℝ)| := by
    intro k a ha
    have ha0 : 0 < a := ha.1
    have ha1 : a ≤ 1 := ha.2
    rcases le_or_gt (0:ℤ) k with hk | hk
    · have hk0 : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a + (k:ℝ)), abs_of_nonneg hk0]
      linarith
    · have hk1 : (k:ℝ) ≤ -1 := by
        have : k ≤ -1 := by omega
        exact_mod_cast this
      have hle : a + (k:ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hle, abs_of_nonpos (by linarith : (k:ℝ) ≤ 0)]
      linarith
  -- Pointwise bound for the integrand, uniform in `a ∈ (0,1]`.
  have hpt : ∀ (k : ℤ) (a : ℝ), a ∈ Set.Ioc (0:ℝ) 1 →
      ‖(φ : ℝ → ℂ) (a + (k:ℝ))‖ ≤ C * (4 * ((1 + |(k:ℝ)|)^2)⁻¹) := by
    intro k a ha
    have h1 : (1 + |a + (k:ℝ)|)^2 ≥ ((1 + |(k:ℝ)|)/2)^2 :=
      pow_le_pow_left₀ (by positivity) (hshift k a ha) 2
    have h2 : C / (1 + |a + (k:ℝ)|)^2 ≤ C / ((1 + |(k:ℝ)|)/2)^2 :=
      div_le_div_of_nonneg_left hCnn (by positivity) h1
    have h3 : C / ((1 + |(k:ℝ)|)/2)^2 = C * (4 * ((1 + |(k:ℝ)|)^2)⁻¹) := by
      field_simp
      ring
    calc ‖(φ : ℝ → ℂ) (a + (k:ℝ))‖ ≤ C / (1 + |a + (k:ℝ)|)^2 := hdec _
      _ ≤ C / ((1 + |(k:ℝ)|)/2)^2 := h2
      _ = C * (4 * ((1 + |(k:ℝ)|)^2)⁻¹) := h3
  -- Integrate the pointwise bound over `(0,1]`, which has measure `1`.
  have hInt : ∀ k : ℤ,
      (∫ a in Set.Ioc (0:ℝ) 1, ‖(φ : ℝ → ℂ) (a + (k:ℝ))‖)
        ≤ C * (4 * ((1 + |(k:ℝ)|)^2)⁻¹) := by
    intro k
    have hs : MeasureTheory.volume (Set.Ioc (0:ℝ) 1) < ⊤ := by
      rw [Real.volume_Ioc]; norm_num
    have hb : ∀ a ∈ Set.Ioc (0:ℝ) 1,
        ‖(‖(φ : ℝ → ℂ) (a + (k:ℝ))‖ : ℝ)‖ ≤ C * (4 * ((1 + |(k:ℝ)|)^2)⁻¹) := by
      intro a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hpt k a ha
    have hmain := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := MeasureTheory.volume)
      (s := Set.Ioc (0:ℝ) 1) (f := fun a => ‖(φ : ℝ → ℂ) (a + (k:ℝ))‖) hs hb
    have hvol : MeasureTheory.volume.real (Set.Ioc (0:ℝ) 1) = 1 := by
      rw [MeasureTheory.Measure.real, Real.volume_Ioc]; norm_num
    rw [Real.norm_eq_abs, hvol, mul_one] at hmain
    exact le_trans (le_abs_self _) hmain
  -- The majorant is summable, so the integrals are.
  have hsum : Summable (fun k : ℤ => C * (4 * ((1 + |(k:ℝ)|)^2)⁻¹)) :=
    summable_four_inv_shift_sq.mul_left C
  apply Summable.of_nonneg_of_le _ hInt hsum
  intro k
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun a ha => norm_nonneg _)

end Work.KMTAreas
