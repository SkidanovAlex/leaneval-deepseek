import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.polya_vinogradov
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda2_estimate

open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-- Pólya–Vinogradov in the form needed downstream: there is an absolute constant `C`
such that for every modulus `q ≥ 2`, every non-principal Dirichlet character `χ` mod `q`,
and every interval `[a, b]` of integers,
`‖∑_{a ≤ n ≤ b} χ(n)‖ ≤ C √q log(2q + 2)`. -/
theorem charSum_range_le_polyaVinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (_hχ : χ ≠ 1)
      (a b : ℕ), a ≤ b →
      ‖∑ n ∈ Finset.Icc a b, χ (n : ZMod q)‖ ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := polya_vinogradov
  refine ⟨2 * C0 + 1, by positivity, ?_⟩
  intro q hq χ hχ a b hab
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hSq : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hL1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hL2 : 0 ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_nonneg; linarith
  have hlogle : Real.log (q : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_le_log hq0; linarith
  -- Prefix sums are bounded by `C0 √q log q` for every length.
  have hpref : ∀ m : ℕ, ‖∑ n ∈ Finset.range m, (χ (n : ZMod q) : ℂ)‖
      ≤ C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hC0pos) hSq) hL1
    · have hm' : m = (m - 1) + 1 := by omega
      rw [hm']
      simpa using hC0 q hq χ hχ (m - 1)
  -- The interval sum is the difference of two prefix sums.
  rw [show Finset.Icc a b = Finset.Ico a (b + 1) from (Finset.Ico_add_one_right_eq_Icc a b).symm]
  rw [Finset.sum_Ico_eq_sub (f := fun n => (χ (n : ZMod q) : ℂ)) (by omega)]
  calc ‖∑ n ∈ Finset.range (b + 1), (χ (n : ZMod q) : ℂ)
          - ∑ n ∈ Finset.range a, (χ (n : ZMod q) : ℂ)‖
      ≤ ‖∑ n ∈ Finset.range (b + 1), (χ (n : ZMod q) : ℂ)‖
          + ‖∑ n ∈ Finset.range a, (χ (n : ZMod q) : ℂ)‖ := norm_sub_le _ _
    _ ≤ C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
          + C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        add_le_add (hpref (b + 1)) (hpref a)
    _ = 2 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by ring
    _ ≤ (2 * C0 + 1) * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by
        have h2C0 : 0 ≤ 2 * C0 := by linarith [hC0pos]
        have hstep1 : 2 * C0 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
            ≤ 2 * C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlogle (mul_nonneg h2C0 hSq)
        have hstep2 : 2 * C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
            ≤ (2 * C0 + 1) * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by
          apply mul_le_mul_of_nonneg_right _ hL2
          exact mul_le_mul_of_nonneg_right (by linarith) hSq
        linarith [hstep1, hstep2]

end Commons.NumberTheory.DirichletCharacter
