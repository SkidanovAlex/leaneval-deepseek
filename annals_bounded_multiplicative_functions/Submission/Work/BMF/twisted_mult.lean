import Mathlib
import Submission.Work.BMF.H6_imports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For every natural number `n` and real `T₀`, the twisted phase `n ^ (-(I * T₀))` has
modulus at most one.  (For `n ≥ 1` it is exactly one; for `n = 0` it is `0`, or `1` in the
degenerate case `T₀ = 0`.) -/
lemma norm_natCast_cpow_neg_I_mul (T₀ : ℝ) (n : ℕ) :
    ‖((n : ℂ) ^ (-(Complex.I * T₀)))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Nat.cast_zero]
    by_cases hc : -(Complex.I * T₀) = 0
    · rw [hc, Complex.cpow_zero]; norm_num
    · rw [Complex.zero_cpow hc]; norm_num
  · rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < (n : ℝ))]
    simp

theorem twisted_mult (f : ℕ → ℂ) (hf : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n)
    (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    (r : ℕ) (χ : DirichletCharacter ℂ r) (T₀ : ℝ) :
    (f 1 * (χ 1) * ((1 : ℕ) : ℂ) ^ (-(Complex.I * T₀)) = 1) ∧
    (∀ m n : ℕ, m.Coprime n →
      f (m * n) * (χ (m * n)) * (((m * n : ℕ) : ℂ) ^ (-(Complex.I * T₀))) =
        (f m * (χ m) * (((m : ℕ) : ℂ) ^ (-(Complex.I * T₀)))) *
          (f n * (χ n) * (((n : ℕ) : ℂ) ^ (-(Complex.I * T₀))))) ∧
    (∀ n : ℕ, ‖f n * (χ n) * (((n : ℕ) : ℂ) ^ (-(Complex.I * T₀)))‖ ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hf1, Complex.one_cpow]
  · intro m n hmn
    have hχ : χ (m * n) = χ m * χ n := by exact map_mul χ _ _
    have htw : (((m * n : ℕ) : ℂ) ^ (-(Complex.I * T₀)))
        = ((m : ℂ) ^ (-(Complex.I * T₀))) * ((n : ℂ) ^ (-(Complex.I * T₀))) := by
      rw [Nat.cast_mul]
      exact Complex.natCast_mul_natCast_cpow m n _
    rw [hχ, htw, hf m n hmn]
    ring
  · intro n
    calc ‖f n * (χ n) * (((n : ℕ) : ℂ) ^ (-(Complex.I * T₀)))‖
        = ‖f n‖ * ‖χ n‖ * ‖((n : ℂ) ^ (-(Complex.I * T₀)))‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * 1 := by
            gcongr
            · exact hb n
            · exact DirichletCharacter.norm_le_one χ _
            · exact norm_natCast_cpow_neg_I_mul T₀ n
      _ = 1 := by norm_num

end Work.BMF
