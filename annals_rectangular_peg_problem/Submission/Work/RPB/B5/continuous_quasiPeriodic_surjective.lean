import Mathlib

namespace Work.RPB.B5

/-- Integer-translate form of the quasi-periodicity relation `f (t + c) = f t + c`:
for every integer `n`, `f (t + n * c) = f t + n * c`.

The proof observes that `t ↦ f t - t` is periodic with period `c`, and a periodic function
is invariant under translation by any integer multiple of its period. -/
theorem quasiPeriodic_int_mul {f : ℝ → ℝ} {c : ℝ} (hper : ∀ t : ℝ, f (t + c) = f t + c)
    (n : ℤ) (t : ℝ) : f (t + (n : ℝ) * c) = f t + (n : ℝ) * c := by
  have hgper : Function.Periodic (fun s : ℝ => f s - s) c := fun s => by
    show f (s + c) - (s + c) = f s - s
    rw [hper s]
    ring
  have h := hgper.int_mul n t
  change f (t + (n : ℝ) * c) - (t + (n : ℝ) * c) = f t - t at h
  linarith [h]

theorem continuous_quasiPeriodic_surjective {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Continuous f) (hper : ∀ t : ℝ, f (t + c) = f t + c) :
    Function.Surjective f := by
  intro y
  -- Choose the integer `n` with `n * c ≤ y - f 0 < (n + 1) * c`.
  set n : ℤ := ⌊(y - f 0) / c⌋ with hn
  have hn1' : (n : ℝ) ≤ (y - f 0) / c := by
    rw [hn]
    exact Int.floor_le _
  have hn2' : (y - f 0) / c < (n : ℝ) + 1 := by
    rw [hn]
    exact Int.lt_floor_add_one _
  have hn1 : (n : ℝ) * c ≤ y - f 0 := (le_div_iff₀ hc).mp hn1'
  have hn2 : y - f 0 < ((n : ℝ) + 1) * c := (div_lt_iff₀ hc).mp hn2'
  -- The values at the endpoints of `[n * c, n * c + c]` bracket `y`.
  have hfa : f ((n : ℝ) * c) = f 0 + (n : ℝ) * c := by
    have h := quasiPeriodic_int_mul hper n 0
    simpa using h
  have hfb : f ((n : ℝ) * c + c) = f 0 + (n : ℝ) * c + c := by
    rw [hper ((n : ℝ) * c), hfa]
  have hIcc : y ∈ Set.Icc (f ((n : ℝ) * c)) (f ((n : ℝ) * c + c)) := by
    refine ⟨?_, ?_⟩
    · rw [hfa]; linarith
    · rw [hfb]; linarith
  -- Intermediate value theorem.
  obtain ⟨t, -, ht⟩ :=
    intermediate_value_Icc (le_add_of_nonneg_right hc.le) hf.continuousOn hIcc
  exact ⟨t, ht⟩

end Work.RPB.B5
