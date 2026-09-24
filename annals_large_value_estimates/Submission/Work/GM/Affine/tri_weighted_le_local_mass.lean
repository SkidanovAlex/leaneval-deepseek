import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.low_freq_defs

/-!
# The triangle-kernel double integral is bounded by the local mass

For `1 ≤ T ≤ Y`, `f : ℝ → ℝ` continuous, nonnegative and compactly supported,

  `∫ z, f z * ∫ u, Y * tri (Y * (z - u)) * f u ≤ Y * ∫ z, f z * ∫_{Icc (z - 1/T) (z + 1/T)} f u`.

The point is that the rescaled triangle kernel `u ↦ Y * tri (Y (z-u))` is supported in
`|z - u| ≤ 1/Y ⊆ [-1/T, 1/T]` and is bounded by `Y` there, so the inner integral is at most
`Y` times the mass of `f` over the interval of radius `1/T` around `z`; multiplying by `f z ≥ 0`
and integrating in `z` gives the claim.
-/

open MeasureTheory

namespace Work.GM.Affine

/-- The triangle (tent) kernel is nonnegative. -/
lemma tri_nonneg (x : ℝ) : 0 ≤ Commons.Analysis.Fourier.tri x := by
  unfold Commons.Analysis.Fourier.tri
  exact le_max_right _ _

/-- The triangle (tent) kernel is at most `1`. -/
lemma tri_le_one (x : ℝ) : Commons.Analysis.Fourier.tri x ≤ 1 := by
  unfold Commons.Analysis.Fourier.tri
  rw [max_le_iff]
  exact ⟨by linarith [abs_nonneg x], by norm_num⟩

/-- For an integrable `f` and `c ≥ 0` the integral of `f` over the moving interval
`[z - c, z + c]` is a continuous function of `z`. -/
lemma continuous_shifted_Icc_integral {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ} (hint : Integrable f) :
    Continuous (fun z : ℝ => ∫ u in Set.Icc (z - c) (z + c), f u) := by
  have hfun : ∀ z : ℝ, (∫ u in Set.Icc (z - c) (z + c), f u) = ∫ u in (z - c)..(z + c), f u := by
    intro z
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  simp only [hfun]
  have hpr : Continuous (fun b : ℝ => ∫ u in (0:ℝ)..b, f u) := hint.continuous_primitive 0
  have h1 : Continuous (fun z : ℝ => ∫ u in (0:ℝ)..(z - c), f u) := hpr.comp (by fun_prop)
  have h2 : Continuous (fun z : ℝ => ∫ u in (0:ℝ)..(z + c), f u) := hpr.comp (by fun_prop)
  have hsplit : ∀ z : ℝ, (∫ u in (z - c)..(z + c), f u)
      = -(∫ u in (0:ℝ)..(z - c), f u) + ∫ u in (0:ℝ)..(z + c), f u := by
    intro z
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hint.intervalIntegrable (a := z - c) (b := 0))
      (hint.intervalIntegrable (a := 0) (b := z + c))
    rw [← h, intervalIntegral.integral_symm]
  simp only [hsplit]
  exact (h1.neg).add h2

theorem tri_weighted_le_local_mass {T Y : ℝ} (hT1 : 1 ≤ T) (hTY : T ≤ Y) {f : ℝ → ℝ}
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f) :
    ∫ z : ℝ, f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u
      ≤ Y * ∫ z : ℝ, f z * (∫ u in Set.Icc (z - 1 / T) (z + 1 / T), f u) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hY0 : 0 < Y := lt_of_lt_of_le hT0 hTY
  have hYnn : 0 ≤ Y := hY0.le
  have hint : Integrable f := hf.integrable_of_hasCompactSupport hcs
  set c : ℝ := 1 / T with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hYc : 1 ≤ Y * c := by
    rw [hc, mul_one_div]
    exact (one_le_div hT0).mpr hTY
  -- Step 1: for fixed `z`, the inner integral is at most `Y` times the local mass at `z`.
  have hΦΨ : ∀ z : ℝ, (∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u)
      ≤ Y * ∫ u in Set.Icc (z - c) (z + c), f u := by
    intro z
    set s : Set ℝ := Set.Icc (z - c) (z + c) with hs
    have hSmeas : MeasurableSet s := by rw [hs]; exact measurableSet_Icc
    have hpoint : ∀ u : ℝ,
        Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u ≤ Y * s.indicator f u := by
      intro u
      by_cases hu : u ∈ s
      · rw [Set.indicator_of_mem hu]
        calc Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u
            ≤ Y * 1 * f u :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (tri_le_one _) hYnn) (hnn u)
          _ = Y * f u := by ring
      · rw [Set.indicator_of_notMem hu]
        -- off the interval the triangle kernel vanishes
        have habs : 1 ≤ |Y * (z - u)| := by
          have hu' : u < z - c ∨ z + c < u := by
            rw [hs, Set.mem_Icc] at hu
            by_cases h : z - c ≤ u
            · right; exact not_le.mp fun h2 => hu ⟨h, h2⟩
            · left; exact not_le.mp h
          rcases hu' with hlt | hgt
          · have h1 : Y * c < Y * (z - u) := mul_lt_mul_of_pos_left (by linarith) hY0
            have h2 : (1:ℝ) ≤ Y * (z - u) := le_trans hYc h1.le
            rw [abs_of_nonneg (by linarith)]; exact h2
          · have h1 : Y * (z - u) < -(Y * c) := by
              have h := mul_lt_mul_of_pos_left (show z - u < -c by linarith) hY0
              rwa [mul_neg] at h
            have h2 : Y * (z - u) ≤ -1 := by linarith
            rw [abs_of_nonpos (by linarith)]; linarith
        rw [Commons.Analysis.Fourier.tri_eq_zero_of_one_le_abs habs]
        simp
    have hint_rhs : Integrable (fun u : ℝ => Y * s.indicator f u) :=
      (hint.indicator hSmeas).const_mul Y
    have h0 : 0 ≤ᵐ[volume] (fun u : ℝ =>
        Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u) :=
      Filter.Eventually.of_forall (fun u => mul_nonneg (mul_nonneg hYnn (tri_nonneg _)) (hnn u))
    have hmono := integral_mono_of_nonneg h0 hint_rhs (Filter.Eventually.of_forall hpoint)
    rw [integral_const_mul, integral_indicator hSmeas] at hmono
    rw [hs] at hmono
    exact hmono
  -- Step 2: integrability of the right-hand integrand, via the continuity of `z ↦ ∫_{z±c} f`.
  have hJcont : Continuous (fun z : ℝ => ∫ u in Set.Icc (z - c) (z + c), f u) :=
    continuous_shifted_Icc_integral hc0 hint
  have hJmeas : AEStronglyMeasurable (fun z : ℝ => ∫ u in Set.Icc (z - c) (z + c), f u) volume :=
    hJcont.aestronglyMeasurable
  have hJbd : ∀ z : ℝ, (∫ u in Set.Icc (z - c) (z + c), f u) ≤ ∫ u, f u := fun z =>
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  have hA0 : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hΨint : Integrable (fun z : ℝ => f z * (Y * ∫ u in Set.Icc (z - c) (z + c), f u)) := by
    refine Integrable.mono' (hint.mul_const (Y * ∫ u, f u)) ?_ ?_
    · exact hf.aestronglyMeasurable.mul (hJmeas.const_mul Y)
    · filter_upwards with z
      have hJnn : 0 ≤ ∫ u in Set.Icc (z - c) (z + c), f u := integral_nonneg hnn
      have h1 : 0 ≤ f z * (Y * ∫ u in Set.Icc (z - c) (z + c), f u) :=
        mul_nonneg (hnn z) (mul_nonneg hYnn hJnn)
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hJbd z) hYnn) (hnn z)
  -- Step 3: multiply by `f z ≥ 0` and integrate in `z`.
  have hΦnn : ∀ z : ℝ,
      0 ≤ ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u := fun z =>
    integral_nonneg (fun u => mul_nonneg (mul_nonneg hYnn (tri_nonneg _)) (hnn u))
  have h1 : 0 ≤ᵐ[volume] (fun z : ℝ =>
      f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u) :=
    Filter.Eventually.of_forall (fun z => mul_nonneg (hnn z) (hΦnn z))
  have h2 : (fun z : ℝ =>
        f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u)
      ≤ᵐ[volume] (fun z : ℝ => f z * (Y * ∫ u in Set.Icc (z - c) (z + c), f u)) :=
    Filter.Eventually.of_forall (fun z => mul_le_mul_of_nonneg_left (hΦΨ z) (hnn z))
  have hmono := integral_mono_of_nonneg h1 hΨint h2
  have hsplit : (fun z : ℝ => f z * (Y * ∫ u in Set.Icc (z - c) (z + c), f u))
      = (fun z : ℝ => Y * (f z * ∫ u in Set.Icc (z - c) (z + c), f u)) := by
    funext z; ring
  rw [hsplit, integral_const_mul] at hmono
  rw [hc] at hmono
  exact hmono

end Work.GM.Affine
