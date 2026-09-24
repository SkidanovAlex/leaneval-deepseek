import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.prime_sum_le_integral

open scoped BigOperators
open MeasureTheory
open intervalIntegral

namespace Work.NumberTheory.Chen.BTermCount

/-- The elementary integral `∫_A^B dt/(t log t) = log log B − log log A` for `2 ≤ A ≤ B`,
obtained from the fundamental theorem of calculus applied to `t ↦ log log t`
(whose derivative is `1/(t log t)`). -/
lemma integral_one_div_mul_log (A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    (∫ t in (A : ℝ)..(B : ℝ), (1 : ℝ) / (t * Real.log t))
      = Real.log (Real.log (B : ℝ)) - Real.log (Real.log (A : ℝ)) := by
  have hAreal : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hA2 : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have ht2 : ∀ t ∈ Set.uIcc (A : ℝ) (B : ℝ), 2 ≤ t := by
    intro t ht
    rw [Set.uIcc_of_le hAreal] at ht
    linarith [ht.1, hA2]
  have hderiv : ∀ t ∈ Set.uIcc (A : ℝ) (B : ℝ),
      HasDerivAt (fun y : ℝ => Real.log (Real.log y)) ((1 : ℝ) / (t * Real.log t)) t := by
    intro t ht
    have h2 : 2 ≤ t := ht2 t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) h2)
    have hl : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2))
    have h1 := (Real.hasDerivAt_log ht0).log hl
    have heq : (t⁻¹) / Real.log t = (1 : ℝ) / (t * Real.log t) := by field_simp
    rwa [heq] at h1
  have hint : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (t * Real.log t)) volume
      (A : ℝ) (B : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc (A : ℝ) (B : ℝ)) :=
      ContinuousOn.log continuousOn_id
        (fun t ht => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (ht2 t ht)))
    have hcont : ContinuousOn (fun t : ℝ => t * Real.log t) (Set.uIcc (A : ℝ) (B : ℝ)) :=
      continuousOn_id.mul hlog
    have hne : ∀ t ∈ Set.uIcc (A : ℝ) (B : ℝ), t * Real.log t ≠ 0 := by
      intro t ht
      exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (ht2 t ht)))
        (ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (ht2 t ht))))
    exact continuousOn_const.div hcont hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- Mertens-type estimate: `∑_{A < p ≤ B} 1/p ≤ log log B − log log A + 4E`, deduced from `prime_sum_le_integral` applied to the constant function `f ≡ 1` (so `g ≡ 0`, the integral is `∫_A^B dt/(t log t) = log log B − log log A`, and the Abel error is `2E(1+1)`). -/
theorem sum_primes_inv_le_loglog (A B : ℕ) (hA : 11 ≤ A) (hAB : A ≤ B)
    (L₀ E : ℝ) (hE : 0 ≤ E)
    (hmer : ∀ t : ℝ, (A : ℝ) ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E) :
    (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ Real.log (Real.log (B : ℝ)) - Real.log (Real.log (A : ℝ)) + 4 * E := by
  have hA2 : 2 ≤ A := by omega
  have hint := integral_one_div_mul_log A B hA2 hAB
  have hmain := prime_sum_le_integral (A := A) (B := B)
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun _ : ℝ => (0 : ℝ)) (L₀ := L₀) (E := E)
      hA2 hAB (fun t _ => hasDerivAt_const t (1 : ℝ)) intervalIntegrable_const
      (fun _ _ => zero_le_one) (Or.inl (fun _ _ => le_refl 0)) hE hmer
  have hmain' : (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ (∫ t in (A : ℝ)..(B : ℝ), (1 : ℝ) / (t * Real.log t))
        + 2 * E * ((1 : ℝ) + (1 : ℝ)) := hmain
  rw [hint] at hmain'
  have h4 : (2 : ℝ) * E * ((1 : ℝ) + (1 : ℝ)) = 4 * E := by ring
  linarith [hmain', h4]

end Work.NumberTheory.Chen.BTermCount
