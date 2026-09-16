import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_char_large_sieve

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

noncomputable section

open Classical

/-- The unitary twist `e(-t log m) = exp((log m · (-t)) · I)` has modulus one. -/
lemma norm_exp_log_twist (m : ℕ) (t : ℝ) :
    ‖Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I)‖ = 1 := by
  rw [show ((Real.log (m : ℝ) * (-t)) * Complex.I : ℂ)
        = (((Real.log (m : ℝ) * (-t) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem bilinear_char_large_sieve_twisted (Q M N : ℕ) (hQ : 1 ≤ Q) (a b : ℕ → ℂ) (t : ℝ) : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ), ‖(∑ m ∈ Finset.Icc 1 M, a m * Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) * χ ((m : ℕ) : ZMod q)) * (∑ n ∈ Finset.Icc 1 N, b n * Complex.exp ((Real.log (n : ℝ) * (-t)) * Complex.I) * χ ((n : ℕ) : ZMod q))‖) ≤ Real.sqrt ((M + Q ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) * Real.sqrt ((N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
  classical
  set a' : ℕ → ℂ := fun m => a m * Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) with ha'
  set b' : ℕ → ℂ := fun n => b n * Complex.exp ((Real.log (n : ℝ) * (-t)) * Complex.I) with hb'
  have ha'_norm : ∀ m, ‖a' m‖ = ‖a m‖ := by
    intro m
    rw [ha', norm_mul, norm_exp_log_twist, mul_one]
  have hb'_norm : ∀ n, ‖b' n‖ = ‖b n‖ := by
    intro n
    rw [hb', norm_mul, norm_exp_log_twist, mul_one]
  have hsum_a : (∑ m ∈ Finset.Icc 1 M, ‖a' m‖ ^ 2) = ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ha'_norm m]
  have hsum_b : (∑ n ∈ Finset.Icc 1 N, ‖b' n‖ ^ 2) = ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hb'_norm n]
  have hLHS : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ),
          ‖(∑ m ∈ Finset.Icc 1 M, a' m * χ ((m : ℕ) : ZMod q)) *
           (∑ n ∈ Finset.Icc 1 N, b' n * χ ((n : ℕ) : ZMod q))‖)
      = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, a' m * b' n * χ (((m * n : ℕ)) : ZMod q)‖ := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    congr 1
    refine Finset.sum_congr ?_ (fun χ hχ => ?_)
    · exact Finset.filter_congr_decidable _ _ _
    · have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : NeZero q := ⟨by omega⟩
      rw [bilinear_char_factor q M N χ a' b']
  have hmain := bilinear_char_large_sieve Q M N hQ a' b'
  calc
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ),
          ‖(∑ m ∈ Finset.Icc 1 M, a' m * χ ((m : ℕ) : ZMod q)) *
           (∑ n ∈ Finset.Icc 1 N, b' n * χ ((n : ℕ) : ZMod q))‖)
        = _ := hLHS
    _ ≤ Real.sqrt ((M + Q ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a' m‖ ^ 2) *
          Real.sqrt ((N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b' n‖ ^ 2) := hmain
    _ = Real.sqrt ((M + Q ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt ((N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
        rw [hsum_a, hsum_b]

end

end Commons.NumberTheory.BombieriVinogradov
