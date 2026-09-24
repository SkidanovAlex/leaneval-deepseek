import Mathlib
import Submission.Work.ChenPlan.H2.SieveDeps

namespace Work.ChenPlan.H2

open Commons.NumberTheory.Chen (Vsieve Vsieve_pos)

/-!
# The lower ratio bound for the Mertens sieve product `Vsieve`

`Vsieve Y = ∏_{3 ≤ p < Y} (1 - 1/(p-1))` is the odd Mertens product of the linear
sieve; by Mertens it satisfies `Vsieve Y ~ L / log Y`.  Consequently, for `s ≤ t`,

`Vsieve s / Vsieve t ≈ log t / log s`,

and here we record the *lower* half of this: with the two-sided rate estimate
`Vsieve u · log u = Vsieve Z · log Z + O(Vsieve Z · log Z / log u)`
(`Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp`, the `A = 1` case)
one gets

`(log t / log s) · (1 - c / log s) ≤ Vsieve s / Vsieve t`

for a suitable constant `c ≥ 0` and all large `s ≤ t`.  The `(1 - c/log s)`
correction is exactly what the sharp two-scale estimate costs.
-/

/-- **Lower ratio bound for `Vsieve`.**  There are `c ≥ 0` and `N₀` with
`(log t / log s)(1 - c/log s) ≤ Vsieve s / Vsieve t` for all `N₀ ≤ s ≤ t`. -/
theorem vsieve_ratio_lower_int :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ N₀ : ℕ, ∀ s t : ℕ, N₀ ≤ s → s ≤ t →
      (Real.log (t : ℝ) / Real.log (s : ℝ)) * (1 - c / Real.log (s : ℝ))
        ≤ Commons.NumberTheory.Chen.Vsieve s / Commons.NumberTheory.Chen.Vsieve t := by
  -- the sharp two-scale rate estimate for `A(s) = Vsieve s · log s`, in the `A = 1` case:
  -- `|A(s) - A(t)| ≤ c · A(t) / log s`
  obtain ⟨c, hcpos, Y₀, hY⟩ :=
    Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp 1 (by norm_num)
  refine ⟨c, hcpos.le, max Y₀ 3, ?_⟩
  intro s t hs hst
  have hs3 : 3 ≤ s := le_trans (le_max_right _ _) hs
  have ht3 : 3 ≤ t := le_trans hs3 hst
  have hsY : Y₀ ≤ s := le_trans (le_max_left _ _) hs
  have hlogs : 0 < Real.log (s:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hVt : 0 < Vsieve t := Vsieve_pos t
  have hdiff := hY s t hsY hst
  rw [Real.rpow_one] at hdiff
  -- `A(s) ≥ A(t) · (1 - c / log s)`, cleared of denominators
  have h1' : -(c * (Vsieve t * Real.log (t:ℝ)))
      ≤ (Vsieve s * Real.log (s:ℝ) - Vsieve t * Real.log (t:ℝ)) * Real.log (s:ℝ) := by
    have h := (abs_le.mp hdiff).1
    rw [← neg_div, div_le_iff₀ hlogs] at h
    linarith [h]
  have hgoal' : Vsieve t * Real.log (t:ℝ) * (Real.log (s:ℝ) - c)
      ≤ Vsieve s * Real.log (s:ℝ) * Real.log (s:ℝ) := by linarith [h1']
  have hL : Vsieve t * Real.log (t:ℝ) * (1 - c/Real.log (s:ℝ)) * Real.log (s:ℝ)
      = Vsieve t * Real.log (t:ℝ) * (Real.log (s:ℝ) - c) := by field_simp
  have hstep : (Real.log (t:ℝ) * Vsieve t) * (1 - c/Real.log (s:ℝ))
      ≤ Vsieve s * Real.log (s:ℝ) := by
    have hkey : Vsieve t * Real.log (t:ℝ) * (1 - c/Real.log (s:ℝ))
        ≤ Vsieve s * Real.log (s:ℝ) :=
      (mul_le_mul_iff_of_pos_right hlogs).mp (by rw [hL]; exact hgoal')
    nlinarith [hkey]
  -- divide by the positive factor `log s · Vsieve t`
  have hpos : (0:ℝ) < Real.log (s:ℝ) * Vsieve t := mul_pos hlogs hVt
  calc (Real.log (t:ℝ)/Real.log (s:ℝ)) * (1 - c/Real.log (s:ℝ))
      = ((Real.log (t:ℝ) * Vsieve t) * (1 - c/Real.log (s:ℝ))) / (Real.log (s:ℝ) * Vsieve t) := by
        field_simp
    _ ≤ (Vsieve s * Real.log (s:ℝ)) / (Real.log (s:ℝ) * Vsieve t) :=
        div_le_div_of_nonneg_right hstep hpos.le
    _ = Vsieve s / Vsieve t := by field_simp

end Work.ChenPlan.H2
