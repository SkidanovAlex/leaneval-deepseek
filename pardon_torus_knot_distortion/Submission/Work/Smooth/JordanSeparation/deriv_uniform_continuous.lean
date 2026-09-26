import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# Uniform continuity of the derivative of a `C¹` closed curve

The derivative `γ'` of a `C¹` `2π`-periodic plane curve is itself `2π`-periodic, and it is
continuous; a continuous periodic function on `ℝ` is uniformly continuous.  This file records
that fact in the `ε`-`δ` form needed by the smooth Jordan separation chapter, and applies it to
the derivative of a `SmoothPlaneCurve`.

The key point is that a continuous `T`-periodic function `f` is determined by its values on the
compact interval `[0, 2T]`: given `a ≤ b` with `b - a ≤ δ ≤ T`, the translate `a - ⌊a/T⌋·T` of `a`
lies in `[0, T)` and the corresponding translate of `b` lies in `[0, 2T]`, and both translates
are `b - a` apart.  Uniform continuity on `[0, 2T]` (Heine–Cantor) then gives the bound, and
periodicity transports it back to `a`, `b`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- A continuous `T`-periodic function `f : ℝ → ℂ` (with `T > 0`) is uniformly continuous, in the
`ε`-`δ` form. -/
theorem uniform_continuous_of_periodic {f : ℝ → ℂ} (hf : Continuous f) {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t t' : ℝ, |t - t'| ≤ δ → ‖f t - f t'‖ ≤ ε := by
  intro ε hε
  have huc : UniformContinuousOn f (Set.Icc 0 (2 * T)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := huc ε hε
  refine ⟨min δ₁ T, lt_min hδ₁pos hT, ?_⟩
  -- the crucial estimate for an ordered pair `a ≤ b`
  have key : ∀ a b : ℝ, a ≤ b → b - a ≤ min δ₁ T → ‖f b - f a‖ ≤ ε := by
    intro a b hab hba
    have hδT : min δ₁ T ≤ T := min_le_right δ₁ T
    have hδδ : min δ₁ T ≤ δ₁ := min_le_left δ₁ T
    set n : ℤ := ⌊a / T⌋ with hn
    have hn_le : (n : ℝ) * T ≤ a := by
      rw [hn]
      exact (le_div_iff₀ hT).mp (Int.floor_le (a / T))
    have hn_lt : a < ((n : ℝ) + 1) * T := by
      rw [hn]
      exact (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (a / T))
    have hmem_a : a - (n : ℝ) * T ∈ Set.Icc 0 (2 * T) := by
      constructor
      · linarith [hn_le]
      · have h1 : a - (n : ℝ) * T < T := by linarith [hn_lt]
        linarith
    have hmem_b : b - (n : ℝ) * T ∈ Set.Icc 0 (2 * T) := by
      constructor
      · linarith [hn_le, hab]
      · have h1 : b - (n : ℝ) * T < T + (min δ₁ T) := by linarith [hn_lt, hba]
        linarith
    have hdist : dist (b - (n : ℝ) * T) (a - (n : ℝ) * T) ≤ δ₁ := by
      have hnn : 0 ≤ (b - (n : ℝ) * T) - (a - (n : ℝ) * T) := by linarith [hab]
      rw [Real.dist_eq, abs_of_nonneg hnn]
      linarith [hba, hδδ]
    have h := hδ₁ (b - (n : ℝ) * T) hmem_b (a - (n : ℝ) * T) hmem_a hdist
    rw [dist_eq_norm] at h
    have hbu : f (b - (n : ℝ) * T) = f b := by
      rw [← hp.int_mul n (b - (n : ℝ) * T),
        show (b - (n : ℝ) * T) + (n : ℝ) * T = b from by ring]
    have hau : f (a - (n : ℝ) * T) = f a := by
      rw [← hp.int_mul n (a - (n : ℝ) * T),
        show (a - (n : ℝ) * T) + (n : ℝ) * T = a from by ring]
    rw [hbu, hau] at h
    exact h
  intro t t' htt'
  rcases le_total t' t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at htt'
    exact key t' t h htt'
  · have h2 : t' - t ≤ min δ₁ T := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at htt'
      linarith
    rw [norm_sub_rev]
    exact key t t' h h2

/-- The derivative of a `C¹` `2π`-periodic plane curve is `2π`-periodic. -/
theorem periodic_deriv (c : Work.Smooth.Jordan.SmoothPlaneCurve) :
    Function.Periodic (deriv c.γ) (2 * Real.pi) := by
  intro t
  have hfun : (fun s : ℝ => c.γ (s + 2 * Real.pi)) = c.γ :=
    funext fun s => c.periodic_apply s
  have h := deriv_comp_add_const c.γ (2 * Real.pi) t
  rw [hfun] at h
  exact h.symm

theorem deriv_uniform_continuous (c : Work.Smooth.Jordan.SmoothPlaneCurve) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t t' : ℝ, |t - t'| ≤ δ → ‖deriv c.γ t - deriv c.γ t'‖ ≤ ε := by
  exact uniform_continuous_of_periodic c.continuous_deriv (by positivity) (periodic_deriv c)

end

end Work.Smooth.JordanSeparation
