import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.SpecialFunctions.Log

open scoped BigOperators
open Set MeasureTheory MeasureSpace intervalIntegral

/-- Telescoping sum over `Ico 1 n` (indices `1, ..., n-1`): sum of `f (x+1) - f x`. -/
private lemma sum_Ico_one_telescope_sub (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.Ico 1 n, (f (x + 1) - f x)) = f n - f 1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show (∑ k ∈ Finset.range (n - 1), (f (1 + k + 1) - f (1 + k))) =
        ∑ k ∈ Finset.range (n - 1), (f (1 + (k + 1)) - f (1 + k)) by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : 1 + k + 1 = 1 + (k + 1) := by omega
        rw [hk']]
  rw [Finset.sum_range_sub (f := fun j : ℕ => f (1 + j))]
  congr 1
  rw [show 1 + (n - 1) = n by omega]

/-- `log (m!)` equals the sum of `log x` for `x = 1, ..., m`. -/
private lemma sum_log_Ico_succ_eq (m : ℕ) :
    (∑ x ∈ Finset.Ico 1 (m + 1), Real.log (x : ℝ)) = Real.log (m.factorial : ℝ) := by
  have hprod : (m.factorial : ℝ) = ∏ x ∈ Finset.Ico 1 (m + 1), (x : ℝ) := by
    rw [← Finset.prod_natCast (Finset.Ico 1 (m + 1)) (fun x : ℕ => x)]
    rw [← Finset.prod_Ico_id_eq_factorial m]
  calc
    (∑ x ∈ Finset.Ico 1 (m + 1), Real.log (x : ℝ)) =
        Real.log (∏ x ∈ Finset.Ico 1 (m + 1), (x : ℝ)) := by
      rw [← Real.log_prod]
      · intro x hx
        have hx1 : 1 ≤ x := (Finset.mem_Ico.mp hx).1
        exact ne_of_gt (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hx1) : 0 < (x : ℝ))
    _ = Real.log (m.factorial : ℝ) := by rw [← hprod]

/-- `log (n!) = log n + log ((n-1)!)` for `n ≥ 1`. -/
private lemma log_factorial_eq_log_mul_pred (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) = Real.log (n : ℝ) + Real.log ((n - 1).factorial : ℝ) := by
  have hfac : n.factorial = n * (n - 1).factorial := by
    rw [← Nat.sub_add_cancel hn, Nat.factorial_succ, Nat.sub_add_cancel hn]
  calc
    Real.log (n.factorial : ℝ) = Real.log (((n * (n - 1).factorial) : ℕ) : ℝ) := by rw [hfac]
    _ = Real.log ((n : ℝ) * ((n - 1).factorial : ℝ)) := by norm_num [Nat.cast_mul]
    _ = Real.log (n : ℝ) + Real.log ((n - 1).factorial : ℝ) := by
      apply Real.log_mul
      · exact_mod_cast (ne_of_gt (by omega : 0 < n))
      · exact_mod_cast (Nat.factorial_ne_zero (n - 1))

/-- `log ((n-1)!)` equals the sum of `log x` for `x = 1, ..., n-1` (i.e. `Ico 1 n`). -/
private lemma sum_log_Ico_eq_log_pred_factorial (n : ℕ) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) = Real.log ((n - 1).factorial : ℝ) := by
  have hsub : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  rw [← hsub]
  exact sum_log_Ico_succ_eq (n - 1)

/-- `log (n!)` equals the sum of `log (x+1)` for `x = 1, ..., n-1` (i.e. `Ico 1 n`). -/
private lemma sum_log_Ico_add_one_eq_log_factorial (n : ℕ) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.Ico 1 n, Real.log ((x + 1 : ℕ) : ℝ)) = Real.log (n.factorial : ℝ) := by
  have htel := sum_Ico_one_telescope_sub (f := fun x : ℕ => Real.log (x : ℝ)) n hn
  have hsum : (∑ x ∈ Finset.Ico 1 n, Real.log ((x + 1 : ℕ) : ℝ)) =
      Real.log (n : ℝ) + (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) := by
    calc
      (∑ x ∈ Finset.Ico 1 n, Real.log ((x + 1 : ℕ) : ℝ))
          = (∑ x ∈ Finset.Ico 1 n, (Real.log ((x + 1 : ℕ) : ℝ) - Real.log (x : ℝ))) +
            (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) := by
            rw [Finset.sum_sub_distrib]
            abel
      _ = (Real.log (n : ℝ) - Real.log ((1 : ℕ) : ℝ)) +
          (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) := by rw [htel]
      _ = Real.log (n : ℝ) + (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) := by
          simp [Real.log_one]
  calc
    (∑ x ∈ Finset.Ico 1 n, Real.log ((x + 1 : ℕ) : ℝ))
        = Real.log (n : ℝ) + (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) := hsum
    _ = Real.log (n : ℝ) + Real.log ((n - 1).factorial : ℝ) := by
        rw [sum_log_Ico_eq_log_pred_factorial n hn]
    _ = Real.log (n.factorial : ℝ) := (log_factorial_eq_log_mul_pred n hn).symm

lemma log_factorial_sub_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Real.log (n.factorial : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) ∧
    Real.log (n.factorial : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hmono : MonotoneOn Real.log (Set.Icc (((1 : ℕ) : ℝ)) (n : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn.mono
    intro x hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (((1 : ℕ) : ℝ))) hx.1
  have hI1 : (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) ≤
      ∫ x in (1 : ℝ)..(n : ℝ), Real.log x := by
    simpa using
      (MonotoneOn.sum_le_integral_Ico (f := Real.log) (a := 1) (b := n) hn1 hmono)
  have hI2 : (∫ x in (1 : ℝ)..(n : ℝ), Real.log x) ≤
      ∑ x ∈ Finset.Ico 1 n, Real.log ((x + 1 : ℕ) : ℝ) := by
    simpa using
      (MonotoneOn.integral_le_sum_Ico (f := Real.log) (a := 1) (b := n) hn1 hmono)
  have hint : (∫ x in (1 : ℝ)..(n : ℝ), Real.log x) =
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 := by
    rw [integral_log]
    rw [Real.log_one]
    ring
  constructor
  · have hlow : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 ≤
        Real.log (n.factorial : ℝ) := by
      calc
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 = ∫ x in (1 : ℝ)..(n : ℝ), Real.log x := by rw [hint]
        _ ≤ ∑ x ∈ Finset.Ico 1 n, Real.log ((x + 1 : ℕ) : ℝ) := hI2
        _ = Real.log (n.factorial : ℝ) := sum_log_Ico_add_one_eq_log_factorial n hn1
    linarith
  · have hup : Real.log (n.factorial : ℝ) ≤
        Real.log (n : ℝ) + ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1) := by
      calc
        Real.log (n.factorial : ℝ) = Real.log (n : ℝ) + Real.log ((n - 1).factorial : ℝ) :=
          log_factorial_eq_log_mul_pred n hn1
        _ = Real.log (n : ℝ) + (∑ x ∈ Finset.Ico 1 n, Real.log (x : ℝ)) := by
          rw [← sum_log_Ico_eq_log_pred_factorial n hn1]
        _ ≤ Real.log (n : ℝ) + ∫ x in (1 : ℝ)..(n : ℝ), Real.log x := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hI1 (Real.log (n : ℝ)))
        _ = Real.log (n : ℝ) + ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1) := by rw [hint]
    linarith

end Commons.Analysis.SpecialFunctions.Log