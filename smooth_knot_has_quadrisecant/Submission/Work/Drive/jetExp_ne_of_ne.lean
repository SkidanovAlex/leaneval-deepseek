import Mathlib
import Submission.Work.Drive.jetDefs

/-!
# Distinct parameters give distinct exponentials

The map `t ↦ jetExp t = e^{i t}` is injective on the half-open interval `[0, 2π)`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

theorem jetExp_ne_of_ne (p q : ℝ) (hp : p ∈ Set.Ico 0 (2 * Real.pi))
    (hq : q ∈ Set.Ico 0 (2 * Real.pi)) (hpq : p ≠ q) : jetExp p ≠ jetExp q := by
  intro heq
  simp only [jetExp] at heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have him : p = q + (n : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    simpa using h
  have h1 : p - q < 2 * Real.pi := by linarith [hp.2, hq.1]
  have h2 : -(2 * Real.pi) < p - q := by linarith [hp.1, hq.2]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hd : (n : ℝ) * (2 * Real.pi) = p - q := by linarith [him]
  have hn_lt : (n : ℝ) < 1 := by
    have h3 : (n : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      rw [hd]; simpa using h1
    exact (mul_lt_mul_iff_of_pos_right hpi).mp h3
  have hn_gt : (-1 : ℝ) < (n : ℝ) := by
    have h3 : (-1 : ℝ) * (2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by
      rw [hd]
      simpa using h2
    exact (mul_lt_mul_iff_of_pos_right hpi).mp h3
  have hn0 : n = 0 := by
    have h3 : (-1 : ℤ) < n := by exact_mod_cast hn_gt
    have h4 : n < (1 : ℤ) := by exact_mod_cast hn_lt
    omega
  subst hn0
  simp only [Int.cast_zero, zero_mul, add_zero] at him
  exact hpq him

end

end Work.Drive
