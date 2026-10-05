import Mathlib

open MeasureTheory

namespace Work.RPCore.Flow

theorem antideriv_bdd (c : ℝ → ℝ) (hc : Continuous c) (h0 : ∀ t, 0 ≤ c t) (h1 : ∀ t, c t ≤ 1) (hleft : ∀ t, t ≤ -2 → c t = 0) (hright : ∀ t, 3 ≤ t → c t = 0) : ∃ B : ℝ, ∀ t, |∫ s in (0 : ℝ)..t, c s| ≤ B := by
  refine ⟨3, fun t => ?_⟩
  have hint : ∀ a b : ℝ, IntervalIntegrable c volume a b := fun a b => hc.intervalIntegrable a b
  -- monotonicity of the antiderivative
  have hmono : ∀ a b : ℝ, a ≤ b → ∫ s in (0 : ℝ)..a, c s ≤ ∫ s in (0 : ℝ)..b, c s := by
    intro a b hab
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)
    have hnn : 0 ≤ ∫ s in a..b, c s :=
      intervalIntegral.integral_nonneg hab (fun u _ => h0 u)
    linarith
  -- bounds at the right end
  have hF3le : ∫ s in (0 : ℝ)..3, c s ≤ 3 := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 3 by norm_num)
      (hint 0 3) intervalIntegrable_const (fun x _ => h1 x)
    simpa using h
  have hF3ge : 0 ≤ ∫ s in (0 : ℝ)..3, c s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => h0 u)
  -- bounds at the left end
  have hFm2le : ∫ s in (0 : ℝ)..(-2), c s ≤ 0 := by
    have hsymm : ∫ s in (0 : ℝ)..(-2), c s = -∫ s in (-2 : ℝ)..0, c s :=
      intervalIntegral.integral_symm (-2) 0
    have hnn : 0 ≤ ∫ s in (-2 : ℝ)..0, c s :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => h0 u)
    linarith
  have hFm2ge : -2 ≤ ∫ s in (0 : ℝ)..(-2), c s := by
    have hsymm : ∫ s in (0 : ℝ)..(-2), c s = -∫ s in (-2 : ℝ)..0, c s :=
      intervalIntegral.integral_symm (-2) 0
    have hle : ∫ s in (-2 : ℝ)..0, c s ≤ 2 := by
      have h := intervalIntegral.integral_mono_on (show (-2 : ℝ) ≤ 0 by norm_num)
        (hint (-2) 0) intervalIntegrable_const (fun x _ => h1 x)
      simpa using h
    linarith
  -- vanishing of the tails
  have hzero_right : ∀ t : ℝ, 3 ≤ t → ∫ s in (3 : ℝ)..t, c s = 0 := by
    intro t ht
    have hcongr : ∫ s in (3 : ℝ)..t, c s = ∫ s in (3 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      simp only [Set.uIoc, Set.mem_Ioc, min_eq_left ht] at hx
      exact hright x (le_of_lt hx.1)
    simpa using hcongr
  have hzero_left : ∀ t : ℝ, t ≤ -2 → ∫ s in (-2 : ℝ)..t, c s = 0 := by
    intro t ht
    have hcongr : ∫ s in (-2 : ℝ)..t, c s = ∫ s in (-2 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      simp only [Set.uIoc, Set.mem_Ioc, max_eq_left ht] at hx
      exact hleft x hx.2
    simpa using hcongr
  rcases le_or_gt t (-2) with ht | ht
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 (-2)) (hint (-2) t)
    rw [hzero_left t ht, add_zero] at hsplit
    rw [← hsplit]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rcases le_or_gt t 3 with ht3 | ht3
    · have hlow := hmono (-2) t (le_of_lt ht)
      have hup := hmono t 3 ht3
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 3) (hint 3 t)
      rw [hzero_right t (le_of_lt ht3), add_zero] at hsplit
      rw [← hsplit]
      exact abs_le.mpr ⟨by linarith, by linarith⟩

end Work.RPCore.Flow
