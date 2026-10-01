import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

noncomputable section

/-- Pointwise bound: for `1 ≤ d ≤ z`, `|λ_d| ≤ log(z/d)`. -/
lemma abs_selLam_le_log {z d : ℕ} (hd1 : 1 ≤ d) (hdz : d ≤ z) :
    |selLam z d| ≤ Real.log ((z : ℝ) / (d : ℝ)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (le_trans hd1 hdz)
  have hge1 : (1 : ℝ) ≤ (z : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdpos]
    have : (1 : ℝ) * (d : ℝ) ≤ (z : ℝ) := by
      rw [one_mul]; exact_mod_cast hdz
    exact this
  have hlog : 0 ≤ Real.log ((z : ℝ) / (d : ℝ)) := Real.log_nonneg hge1
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [← Int.cast_abs]
    exact_mod_cast h
  calc |selLam z d|
      = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |Real.log ((z : ℝ) / (d : ℝ))| := by
        rw [selLam, abs_mul]
    _ ≤ 1 * |Real.log ((z : ℝ) / (d : ℝ))| :=
        mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    _ = Real.log ((z : ℝ) / (d : ℝ)) := by rw [one_mul, abs_of_nonneg hlog]

/-- For `n ≥ 1`, `n * log ((n+1)/n) ≤ 1`. -/
lemma mul_log_succ_div_le_one {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) by positivity)
    have h2 : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp
      ring
    linarith [h, h2]
  calc (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ))
      ≤ (n : ℝ) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hnpos)
    _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hnpos)]

/-- `Σ_{d ≤ z} log(z/d) ≤ z`. -/
lemma sum_log_div_le (z : ℕ) (hz : 1 ≤ z) :
    (∑ d ∈ Finset.Icc 1 z, Real.log ((z : ℝ) / (d : ℝ))) ≤ (z : ℝ) := by
  have hF : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * Real.log (n : ℝ) - (∑ d ∈ Finset.Icc 1 n, Real.log (d : ℝ)) ≤ (n : ℝ) := by
    intro n hn
    refine Nat.le_induction ?base ?step n hn
    · simp
    · intro m hm ih
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      push_cast
      have hlog : Real.log (((m : ℝ) + 1) / (m : ℝ))
          = Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) :=
        Real.log_div (by positivity) (by exact_mod_cast (ne_of_gt (by omega : 0 < m)))
      have hinc : (m : ℝ) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) ≤ 1 := by
        rw [← hlog]; exact mul_log_succ_div_le_one hm
      have hmain : (m : ℝ) * Real.log ((m : ℝ) + 1)
            - (∑ d ∈ Finset.Icc 1 m, Real.log (d : ℝ)) ≤ (m : ℝ) + 1 := by
        have heq : (m : ℝ) * Real.log ((m : ℝ) + 1)
              - (∑ d ∈ Finset.Icc 1 m, Real.log (d : ℝ))
            = ((m : ℝ) * Real.log (m : ℝ)
                - (∑ d ∈ Finset.Icc 1 m, Real.log (d : ℝ)))
              + (m : ℝ) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
        rw [heq]; linarith [ih, hinc]
      have heq2 : ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1)
            - ((∑ d ∈ Finset.Icc 1 m, Real.log (d : ℝ)) + Real.log ((m : ℝ) + 1))
          = (m : ℝ) * Real.log ((m : ℝ) + 1)
            - (∑ d ∈ Finset.Icc 1 m, Real.log (d : ℝ)) := by ring
      rw [heq2]; exact hmain
  have hT : (∑ d ∈ Finset.Icc 1 z, Real.log ((z : ℝ) / (d : ℝ)))
      = (z : ℝ) * Real.log (z : ℝ) - (∑ d ∈ Finset.Icc 1 z, Real.log (d : ℝ)) := by
    have hterm : ∀ d ∈ Finset.Icc 1 z,
        Real.log ((z : ℝ) / (d : ℝ)) = Real.log (z : ℝ) - Real.log (d : ℝ) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hz0 : (z : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (by omega : 0 < z))
      have hd0 : (d : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (by omega : 0 < d))
      exact Real.log_div hz0 hd0
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const]
    have hcard : (Finset.Icc 1 z).card = z := by rw [Nat.card_Icc]; omega
    rw [hcard, nsmul_eq_mul]
  rw [hT]
  exact hF z hz

theorem sum_abs_selLam_le (z : ℕ) (hz : 1 ≤ z) :
    (∑ d ∈ Finset.Icc 1 z, |selLam z d|) ≤ (z : ℝ) := by
  calc (∑ d ∈ Finset.Icc 1 z, |selLam z d|)
      ≤ ∑ d ∈ Finset.Icc 1 z, Real.log ((z : ℝ) / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact abs_selLam_le_log (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    _ ≤ (z : ℝ) := sum_log_div_le z hz

end

end Work.LinnikAreas.Density4
