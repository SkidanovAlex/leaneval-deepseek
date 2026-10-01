import Mathlib
import Submission.Work.LinnikAreas.Density4.ExpSqrtLogAux
import Submission.Work.LinnikAreas.Density4.Est.Fq_mul_sub_le_Gq
import Submission.Work.LinnikAreas.Density4.Est.sum_inv_sub_log_le_one

namespace Work.LinnikAreas.Density4

lemma t_nonneg {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    0 ≤ Real.log ((N:ℝ)/(n:ℝ)) := by
  apply Real.log_nonneg
  rw [one_le_div (by exact_mod_cast (by omega : 0 < n))]
  exact_mod_cast hnN

lemma t_anti {m n N : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.log ((N:ℝ)/(n:ℝ)) ≤ Real.log ((N:ℝ)/(m:ℝ)) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (show (0:ℕ) < m by omega)
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show (0:ℕ) < n by omega)
  apply Real.log_le_log
  · exact div_pos hN0 hn0
  · have hNnn : (0:ℝ) ≤ N := by positivity
    exact div_le_div_of_nonneg_left hNnn hm0 (by exact_mod_cast hmn)

lemma t_sub {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    Real.log ((N:ℝ)/(n:ℝ)) - Real.log ((N:ℝ)/((n:ℝ)+1)) = Real.log (((n:ℝ)+1)/(n:ℝ)) := by
  have hN0 : (N:ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn10 : ((n:ℝ)+1) ≠ 0 := by positivity
  rw [← Real.log_div (div_ne_zero hN0 hn0) (div_ne_zero hN0 hn10)]
  congr 1
  field_simp

/-- The logarithmic remainder `log((n+1)/n)` never exceeds `1/n`. -/
lemma log_succ_div_le_inv {n : ℕ} (hn : 1 ≤ n) :
    Real.log (((n:ℝ)+1)/(n:ℝ)) ≤ (1:ℝ)/(n:ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 < ((n:ℝ)+1)/(n:ℝ) := div_pos (by linarith) hnpos
  have h := Real.log_le_sub_one_of_pos hx
  have hx1 : ((n:ℝ)+1)/(n:ℝ) - 1 = (1:ℝ)/(n:ℝ) := by
    field_simp
    ring
  linarith [h, hx1]

theorem sum_inv_exp_neg_sqrt_log_div (c : ℝ) (hc : 0 < c) : ∃ K : ℝ, 0 < K ∧
    ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N,
          (1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ)))))) ≤ K := by
  refine ⟨2/c^2 + 2, by positivity, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  let t : ℕ → ℝ := fun n => Real.log ((N:ℝ)/(n:ℝ))
  have hS : (∑ n ∈ Finset.Icc 1 N,
        (1/(n:ℝ)) * Real.exp (-(c * Real.sqrt (Real.log ((N:ℝ)/(n:ℝ))))))
      = ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * Fq c (t n) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [Fq, t]
  rw [hS]
  have hdecomp : (∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * Fq c (t n))
      = (∑ n ∈ Finset.Icc 1 N, (t n - t (n+1)) * Fq c (t n))
        + (∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ) - (t n - t (n+1))) * Fq c (t n)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hdecomp]
  have hB : (∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ) - (t n - t (n+1))) * Fq c (t n)) ≤ 1 := by
    calc (∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ) - (t n - t (n+1))) * Fq c (t n))
        ≤ ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ) - Real.log (((n:ℝ)+1)/(n:ℝ))) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hΔt : t n - t (n+1) = Real.log (((n:ℝ)+1)/(n:ℝ)) := by
            simp only [t]
            have h := t_sub hN hn.1
            push_cast
            exact h
          rw [hΔt]
          have hle1 : Fq c (t n) ≤ 1 := Fq_le_one c hc (by
            simp only [t]; exact t_nonneg hn.1 hn.2)
          have hnn : 0 ≤ (1:ℝ)/(n:ℝ) - Real.log (((n:ℝ)+1)/(n:ℝ)) := by
            linarith [log_succ_div_le_inv hn.1]
          nlinarith [hle1, hnn]
      _ ≤ 1 := Est.sum_inv_sub_log_le_one hN
  have hA : (∑ n ∈ Finset.Icc 1 N, (t n - t (n+1)) * Fq c (t n)) ≤ 2/c^2 + 1 := by
    have hsplit := Finset.sum_Icc_succ_top (a := 1) (b := N-1) (by omega)
        (fun n => (t n - t (n+1)) * Fq c (t n))
    rw [show N - 1 + 1 = N by omega] at hsplit
    rw [hsplit]
    have hterm : (t N - t (N+1)) * Fq c (t N) ≤ 1 := by
      have htN : t N = 0 := by
        simp only [t]
        rw [div_self (by exact_mod_cast (by omega : N ≠ 0)), Real.log_one]
      have hΔt : t N - t (N+1) = Real.log (((N:ℝ)+1)/(N:ℝ)) := by
        simp only [t]
        have h := t_sub hN hN
        push_cast
        exact h
      rw [hΔt, htN, Fq_zero, mul_one]
      have hNpos' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
      have hx : 0 < ((N:ℝ)+1)/(N:ℝ) := div_pos (by linarith) hNpos'
      have h := Real.log_le_sub_one_of_pos hx
      have hx1 : ((N:ℝ)+1)/(N:ℝ) - 1 = (1:ℝ)/(N:ℝ) := by
        field_simp
        ring
      have h1 : (1:ℝ)/(N:ℝ) ≤ 1 := by
        rw [div_le_one hNpos']; exact_mod_cast hN
      linarith [h, hx1, h1]
    have hpart1 : (∑ n ∈ Finset.Icc 1 (N-1), (t n - t (n+1)) * Fq c (t n))
        ≤ Gq c (t 1) - Gq c (t N) := by
      have hle : (∑ n ∈ Finset.Icc 1 (N-1), (t n - t (n+1)) * Fq c (t n))
          ≤ ∑ n ∈ Finset.Icc 1 (N-1), (Gq c (t n) - Gq c (t (n+1))) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Icc] at hn
        have htn1 : 0 ≤ t (n+1) := by
          simp only [t]; exact t_nonneg (by omega) (by omega)
        have htle : t (n+1) ≤ t n := by
          simp only [t]; exact t_anti hNpos hn.1 (by omega)
        have hkey := Est.Fq_mul_sub_le_Gq (a := t (n+1)) (b := t n) c hc htn1 htle
        calc (t n - t (n+1)) * Fq c (t n) = Fq c (t n) * (t n - t (n+1)) := by ring
          _ ≤ Gq c (t n) - Gq c (t (n+1)) := hkey
      refine hle.trans ?_
      rw [show Finset.Icc 1 (N-1) = Finset.Ico 1 N by
              ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      rw [show (∑ n ∈ Finset.Ico 1 N, (Gq c (t n) - Gq c (t (n+1))))
            = -(∑ n ∈ Finset.Ico 1 N, (Gq c (t (n+1)) - Gq c (t n))) by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl; intro n _; ring]
      rw [Finset.sum_Ico_sub (fun k => Gq c (t k)) hN]
      exact le_of_eq (by ring)
    have hGbound : Gq c (t 1) - Gq c (t N) ≤ 2/c^2 := by
      have htN : t N = 0 := by
        simp only [t]
        rw [div_self (by exact_mod_cast (by omega : N ≠ 0)), Real.log_one]
      have ht1 : 0 ≤ t 1 := by simp only [t]; exact t_nonneg le_rfl hN
      have hg1 : Gq c (t 1) ≤ 0 := Gq_nonpos c hc ht1
      rw [htN, Gq_zero c hc]
      linarith
    linarith [hpart1, hGbound, hterm]
  linarith [hA, hB]

end Work.LinnikAreas.Density4
