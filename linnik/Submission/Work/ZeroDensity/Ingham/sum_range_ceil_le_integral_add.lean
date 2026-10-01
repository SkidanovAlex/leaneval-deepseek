import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Head (increasing) part of the unimodal sum/integral comparison: if `0 < x₀`, `f` is
nonnegative on `(0,∞)`, monotone on `[0,x₀]` and integrable on `(0,∞)`, then the sum of `f` over
the naturals `n < ⌈x₀⌉₊` is bounded by `∫_{(0,∞)} f + f x₀`. -/
theorem sum_range_ceil_le_integral_add {f : ℝ → ℝ} {x₀ : ℝ} (hx : 0 < x₀)
    (hmono : MonotoneOn f (Set.Icc 0 x₀))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)))
    (hnn : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ f x) :
    ∑ i ∈ Finset.range (⌈x₀⌉₊), f i ≤
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) f + f x₀ := by
  set N : ℕ := ⌈x₀⌉₊ with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.ceil_pos.mpr hx
  have hNlt : (N : ℝ) < x₀ + 1 := by rw [hN]; exact Nat.ceil_lt_add_one hx.le
  -- write `N = m + 1` so that the last term of the sum is `f m` for a natural `m`
  obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm_lt : (m : ℝ) < x₀ := by
    have : (m : ℝ) = (N : ℝ) - 1 := by rw [hm]; push_cast; ring
    linarith
  have hm_le : (m : ℝ) ≤ x₀ := le_of_lt hm_lt
  rw [hm, Finset.sum_range_succ]
  -- monotonicity restricted to `[0, m]`, in the exact shape the Mathlib lemma expects
  have hmono' : MonotoneOn f (Set.Icc ((0:ℕ):ℝ) (m:ℝ)) := by
    refine hmono.mono ?_
    intro x hx'
    exact ⟨by simpa using hx'.1, le_trans hx'.2 hm_le⟩
  -- sum/integral comparison on `[0, m]`
  have hsum : ∑ x ∈ Finset.Ico 0 m, f x ≤ ∫ x in (0:ℝ)..(m:ℝ), f x := by
    simpa using MonotoneOn.sum_le_integral_Ico (a := 0) (b := m) (f := f) (Nat.zero_le _) hmono'
  rw [Nat.Ico_zero_eq_range] at hsum
  -- the leftover last term is bounded by `f x₀` by monotonicity
  have hflast : f m ≤ f x₀ := hmono ⟨by positivity, hm_le⟩ ⟨le_of_lt hx, le_rfl⟩ hm_le
  -- the interval integral is dominated by the integral over `(0, ∞)`
  have hint_le : ∫ x in (0:ℝ)..(m:ℝ), f x ≤
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) f := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    apply MeasureTheory.setIntegral_mono_set hint
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hnn
    · exact Filter.Eventually.of_forall (fun x (hx : x ∈ Set.Ioc (0:ℝ) (m:ℝ)) => hx.1)
  have hsum2 : ∑ x ∈ Finset.range m, f x ≤
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) f :=
    le_trans hsum hint_le
  exact add_le_add hsum2 hflast

end Work.ZeroDensity.Ingham
