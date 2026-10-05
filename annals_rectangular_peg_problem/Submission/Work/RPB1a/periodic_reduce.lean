import Mathlib

namespace Work.RPB1a

/-- A `2π`-periodic function takes the same value at `x + n * 2π` as at `x`, for every
integer `n`. -/
lemma periodic_add_int_mul_two_pi (u : ℝ → ℂ)
    (hper : ∀ t : ℝ, u (t + 2 * Real.pi) = u t) (x : ℝ) (n : ℤ) :
    u (x + n * (2 * Real.pi)) = u x := by
  have hp : Function.Periodic u (2 * Real.pi) := hper
  exact hp.int_mul n x

/-- **Periodic reduction.** For a `2π`-periodic `u` and any real `t`, one can find `t₀` in
`[0, 2π]` such that all the "chord lengths to the base point" attached at `t` coincide with
those attached at `t₀`. -/
theorem periodic_reduce (u : ℝ → ℂ) (hper : ∀ t : ℝ, u (t + 2 * Real.pi) = u t) (t : ℝ) :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ∀ h : ℝ, ‖u (t + h) - u t‖ = ‖u (t₀ + h) - u t₀‖ := by
  -- The representative of `t` modulo `2π`.
  set t₀ : ℝ := (2 * Real.pi) * Int.fract (t / (2 * Real.pi)) with ht₀
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpos
  refine ⟨t₀, ?_, ?_⟩
  · rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [ht₀]
      exact mul_nonneg hpos.le (Int.fract_nonneg _)
    · rw [ht₀]
      calc (2 * Real.pi) * Int.fract (t / (2 * Real.pi))
          ≤ (2 * Real.pi) * 1 :=
            mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le hpos.le
        _ = 2 * Real.pi := mul_one _
  · intro h
    set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
    -- `t = t₀ + n * 2π`.
    have hdecomp : t = t₀ + n * (2 * Real.pi) := by
      have hf : Int.fract (t / (2 * Real.pi)) + (n : ℝ) = t / (2 * Real.pi) := by
        rw [hn]; exact Int.fract_add_floor _
      have hmul : (2 * Real.pi) * (Int.fract (t / (2 * Real.pi)) + (n : ℝ)) = t := by
        rw [hf, mul_div_cancel₀ t hne]
      have halg : (2 * Real.pi) * Int.fract (t / (2 * Real.pi))
          + (n : ℝ) * (2 * Real.pi) = t := by
        have hstep : (2 * Real.pi) * Int.fract (t / (2 * Real.pi))
            + (n : ℝ) * (2 * Real.pi)
            = (2 * Real.pi) * (Int.fract (t / (2 * Real.pi)) + (n : ℝ)) := by ring
        rw [hstep, hmul]
      rw [ht₀]; exact halg.symm
    have hu1 : u t = u t₀ := by
      rw [hdecomp]
      exact periodic_add_int_mul_two_pi u hper t₀ n
    have hu2 : u (t + h) = u (t₀ + h) := by
      have harg : t + h = (t₀ + h) + n * (2 * Real.pi) := by rw [hdecomp]; ring
      rw [harg]
      exact periodic_add_int_mul_two_pi u hper (t₀ + h) n
    rw [hu1, hu2]

end Work.RPB1a
