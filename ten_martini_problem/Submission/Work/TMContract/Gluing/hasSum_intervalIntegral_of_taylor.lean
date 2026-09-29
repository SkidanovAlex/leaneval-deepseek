import Mathlib

open MeasureTheory

namespace Work.TMContract.Gluing

/-- If `φ x = ∑ₘ c_m x Eᵐ` for every `x ∈ (s,t)`, the coefficients `c_m` are continuous on
`[s,t]` and dominated uniformly by `C ρ^{-m}` with `|E| < ρ`, then the interval integral of `φ`
is the sum of the interval integrals of the coefficients against `Eᵐ`.  This is the dominated
convergence theorem for parametric interval integrals
(`intervalIntegral.hasSum_integral_of_dominated_convergence`): the dominating series
`∑ₘ C (|E|/ρ)ᵐ` converges because `|E| < ρ`. -/
theorem hasSum_intervalIntegral_of_taylor {φ : ℝ → ℝ} {c : ℕ → ℝ → ℝ} {s t E ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 < C) (hst : s < t)
    (hc : ∀ m, ContinuousOn (c m) (Set.Icc s t))
    (hbound : ∀ m x, x ∈ Set.Icc s t → |c m x| ≤ C * (1 / ρ) ^ m)
    (hexp : ∀ x ∈ Set.Ioo s t, HasSum (fun m => c m x * E ^ m) (φ x))
    (hE : |E| < ρ) :
    HasSum (fun m => (∫ x in s..t, c m x) * E ^ m) (∫ x in s..t, φ x) := by
  -- the geometric ratio `|E| / ρ` is `< 1`, so the dominating series converges
  have hr0 : 0 ≤ |E| * (1 / ρ) := by positivity
  have hr1 : |E| * (1 / ρ) < 1 := by
    rw [mul_one_div, div_lt_one hρ]; exact hE
  have hsum : Summable (fun n : ℕ => C * (1 / ρ) ^ n * |E| ^ n) := by
    have hrw : (fun n : ℕ => C * (1 / ρ) ^ n * |E| ^ n) =
        fun n : ℕ => C * (|E| * (1 / ρ)) ^ n := by
      funext n; rw [mul_pow]; ring
    rw [hrw]
    exact Summable.mul_left C
      (summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]))
  -- `Ι s t = Ioc s t ⊆ Icc s t`
  have hsub : Set.uIoc s t ⊆ Set.Icc s t := by
    rw [Set.uIoc_of_le hst.le]; exact Set.Ioc_subset_Icc_self
  have hF_meas : ∀ n, AEStronglyMeasurable (fun x : ℝ => c n x * E ^ n)
      (volume.restrict (Set.uIoc s t)) := fun n =>
    ContinuousOn.aestronglyMeasurable_of_subset_isCompact ((hc n).mul_const (E ^ n))
      isCompact_Icc measurableSet_uIoc hsub
  have h_bound : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc s t →
      ‖c n x * E ^ n‖ ≤ C * (1 / ρ) ^ n * |E| ^ n := by
    intro n
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx' : x ∈ Set.Icc s t := hsub hx
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (hbound n x hx') (by have := hC; positivity)
  have h_sum_bound : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc s t →
      Summable (fun n => C * (1 / ρ) ^ n * |E| ^ n) :=
    Filter.Eventually.of_forall (fun x _ => hsum)
  have h_int_bound : IntervalIntegrable (fun _ : ℝ => (∑' n, C * (1 / ρ) ^ n * |E| ^ n))
      volume s t := intervalIntegrable_const
  -- the pointwise expansion holds almost everywhere on `Ioc s t`: the only exceptional point
  -- is the right endpoint `t`, a null set
  have h_lim : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc s t →
      HasSum (fun n => c n x * E ^ n) (φ x) := by
    have hnot : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ t := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ (measure_singleton t)
      intro x hx
      simpa using hx
    filter_upwards [hnot] with x hxne hxmem
    have hxIoc : x ∈ Set.Ioc s t := by rwa [Set.uIoc_of_le hst.le] at hxmem
    exact hexp x ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxne⟩
  have hmain := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := s) (b := t) (f := φ) (F := fun n x => c n x * E ^ n)
    (fun n _ => C * (1 / ρ) ^ n * |E| ^ n)
    hF_meas h_bound h_sum_bound h_int_bound h_lim
  simpa using hmain

end Work.TMContract.Gluing
