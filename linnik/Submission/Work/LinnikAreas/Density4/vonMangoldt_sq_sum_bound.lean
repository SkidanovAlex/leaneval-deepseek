import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real
import Submission.Work.LinnikAreas.Density4.psi_eventually_le_of_powLog_two
import Submission.Work.LinnikAreas.Density4.exists_bound_of_eventually_mono

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- `ψ(N)` rewritten as the sum of `Λ` over `1 ≤ n ≤ N`. -/
lemma psi_eq_sum_Icc_one (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have h : Finset.Icc (0 : ℕ) N = insert 0 (Finset.Icc 1 N) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert (by simp)]
  simp

/-- Second moment of `Λ` up to `N` is at most `log N · ψ(N)`
(the `n = 1` term is `0` and `Λ n ≤ log n ≤ log N`). -/
lemma sum_sq_le_log_mul_psi (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ Real.log (N : ℝ) * Chebyshev.psi (N : ℝ) := by
  rw [psi_eq_sum_Icc_one, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hΛnn : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log (N : ℝ) := by
    refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < n)
    · exact_mod_cast hnN
  calc ArithmeticFunction.vonMangoldt n ^ 2
      = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt n := by ring
    _ ≤ ArithmeticFunction.vonMangoldt n * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_left hlog hΛnn
    _ = Real.log (N : ℝ) * ArithmeticFunction.vonMangoldt n := by ring

/-- The partial second moment of `Λ` is monotone in `N`. -/
lemma sum_sq_mono {N M : ℕ} (h : N ≤ M) :
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ ∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n) ^ 2 := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right h
  · intro i _ _
    positivity

/-- Arithmetic core: for `N ≥ 3`, `log N · (N + N/log²N) ≤ N log N + N`. -/
lemma log_mul_div_log_sq_le (N : ℕ) (hN : 3 ≤ N) :
    Real.log (N : ℝ) * ((N : ℝ) + (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ))
      ≤ (N : ℝ) * Real.log (N : ℝ) + (N : ℝ) := by
  have hx : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hxpos : 0 < (N : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by linarith [Real.exp_one_lt_three]
    exact (Real.le_log_iff_exp_le hxpos).2 h3
  have hLpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  rw [Real.rpow_two]
  have hEq : Real.log (N : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
      = (N : ℝ) / Real.log (N : ℝ) := by
    field_simp
  have hdiv : (N : ℝ) / Real.log (N : ℝ) ≤ (N : ℝ) := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hthis : Real.log (N : ℝ) * ((N : ℝ) + (N : ℝ) / (Real.log (N : ℝ)) ^ 2)
      = Real.log (N : ℝ) * (N : ℝ)
        + Real.log (N : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
  rw [hthis, hEq]
  linarith

/-- Second moment of von Mangoldt, from PNT with log-power error.  Import
Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real: it gives psi x - x = O(x / log^A x). -/
theorem vonMangoldt_sq_sum_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ (N : ℝ) * Real.log (N : ℝ) + C * (N : ℝ) := by
  -- The prime number theorem with a log-power error term, exponent `2`.
  have hpsi : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ x / (Real.log x) ^ (2 : ℝ) :=
    Commons.NumberTheory.Zeta.psi_sub_id_powLog_real 2 (by norm_num)
  -- Hence `ψ N ≤ N + N/log²N` for all large `N`.
  obtain ⟨M, _hM3, hMbound⟩ := psi_eventually_le_of_powLog_two hpsi
  -- Combine: bound on `[1, M]` by a constant, the asymptotic bound beyond `M`.
  refine exists_bound_of_eventually_mono
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
    (fun _ _ hab => sum_sq_mono hab) M ?_
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  calc (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ Real.log (N : ℝ) * Chebyshev.psi (N : ℝ) := sum_sq_le_log_mul_psi N
    _ ≤ Real.log (N : ℝ) *
          ((N : ℝ) + (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (hMbound N hN)
        exact Real.log_nonneg (by exact_mod_cast hN1)
    _ ≤ (N : ℝ) * Real.log (N : ℝ) + (N : ℝ) := log_mul_div_log_sq_le N hN3

end Work.LinnikAreas.Density4
