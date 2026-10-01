import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_Dg_le
import Submission.Work.LinnikAreas.Density4.thetaDiag_tdH_nonneg
import Submission.Work.LinnikAreas.Density4.tdH_sum_le_Gamma

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

theorem tdDg_sum_le (M σ A : ℝ) (hM : 0 < M) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A)
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, Work.LinnikAreas.Density4.tdDg M n * Work.LinnikAreas.Density4.tdH σ A n)
      ≤ M * (Real.Gamma σ * A ^ σ)
        - (∑ n ∈ Finset.Icc 2 (min N ⌊Real.exp M⌋₊),
            (M - Real.log (n:ℝ) - 1) * Work.LinnikAreas.Density4.tdH σ A n)
        + (Real.Gamma σ * A ^ σ) := by
  set k := min N ⌊Real.exp M⌋₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk]
    refine le_min (by omega) (Nat.le_floor ?_)
    rw [Nat.cast_one]
    exact le_of_lt (Real.one_lt_exp_iff.mpr hM)
  have hk_le_N : k ≤ N := by rw [hk]; exact min_le_left _ _
  have hsplit : Finset.Icc 2 N = Finset.Icc 2 k ∪ Finset.Icc (k+1) N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro hn
      by_cases hnk : n ≤ k
      · exact Or.inl ⟨hn.1, hnk⟩
      · exact Or.inr ⟨by omega, hn.2⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · exact ⟨h1, le_trans h2 hk_le_N⟩
      · exact ⟨by omega, h2⟩
  have hdisj : Disjoint (Finset.Icc 2 k) (Finset.Icc (k+1) N) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  have hsum_split : ∀ (g : ℕ → ℝ),
      (∑ n ∈ Finset.Icc 2 N, g n) = (∑ n ∈ Finset.Icc 2 k, g n) + (∑ n ∈ Finset.Icc (k+1) N, g n) := by
    intro g
    rw [hsplit, Finset.sum_union hdisj]
  have hstep1 : (∑ n ∈ Finset.Icc 2 N, tdDg M n * tdH σ A n)
      ≤ ∑ n ∈ Finset.Icc 2 N, (tdG M n + 1) * tdH σ A n := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (thetaDiag_Dg_le M hM n (Finset.mem_Icc.mp hn).1)
      (thetaDiag_tdH_nonneg σ A n)
  have hlog_le : ∀ n ∈ Finset.Icc 2 k, tdG M n = Real.log (n:ℝ) := by
    intro n hn
    have hnk : n ≤ ⌊Real.exp M⌋₊ := le_trans (Finset.mem_Icc.mp hn).2 (by rw [hk]; exact min_le_right _ _)
    have hnpos : (0:ℝ) < n := by
      have : (1:ℕ) ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      exact_mod_cast this
    have h1 : (n:ℝ) ≤ Real.exp M := le_trans (by exact_mod_cast hnk) (Nat.floor_le (Real.exp_pos M).le)
    have hlogM : Real.log (n:ℝ) ≤ M := by
      calc Real.log (n:ℝ) ≤ Real.log (Real.exp M) := Real.log_le_log hnpos h1
        _ = M := Real.log_exp M
    rw [tdG, min_eq_left hlogM]
  have hstep3 : (∑ n ∈ Finset.Icc 2 k, (tdG M n + 1) * tdH σ A n)
      = M * (∑ n ∈ Finset.Icc 2 k, tdH σ A n)
        - (∑ n ∈ Finset.Icc 2 k, (M - Real.log (n:ℝ) - 1) * tdH σ A n) := by
    have hcongr : ∀ n ∈ Finset.Icc 2 k,
        (tdG M n + 1) * tdH σ A n = M * tdH σ A n - (M - Real.log (n:ℝ) - 1) * tdH σ A n := by
      intro n hn
      rw [hlog_le n hn]; ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, Finset.mul_sum]
  have hstep4 : (∑ n ∈ Finset.Icc (k+1) N, (tdG M n + 1) * tdH σ A n)
      ≤ (M+1) * (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_right _ (thetaDiag_tdH_nonneg σ A n)
    have hg : tdG M n ≤ M := by rw [tdG]; exact min_le_right _ _
    linarith
  have hSbound : (∑ n ∈ Finset.Icc 2 N, tdH σ A n) ≤ Real.Gamma σ * A^σ :=
    tdH_sum_le_Gamma σ A hσ hσ1 (by linarith) N
  have hSk_sum : (∑ n ∈ Finset.Icc 2 k, tdH σ A n) + (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n)
      ≤ Real.Gamma σ * A^σ := by
    rw [← hsum_split (fun n => tdH σ A n)]
    exact hSbound
  have hSk_nn : 0 ≤ (∑ n ∈ Finset.Icc 2 k, tdH σ A n) :=
    Finset.sum_nonneg (fun n _ => thetaDiag_tdH_nonneg σ A n)
  have hSk'_le : (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n) ≤ Real.Gamma σ * A^σ := by linarith
  have hstep6 : M * (∑ n ∈ Finset.Icc 2 k, tdH σ A n) + (M+1) * (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n)
      ≤ M * (Real.Gamma σ * A^σ) + (Real.Gamma σ * A^σ) := by
    have h1 : M * ((∑ n ∈ Finset.Icc 2 k, tdH σ A n) + (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n))
        ≤ M * (Real.Gamma σ * A^σ) := mul_le_mul_of_nonneg_left hSk_sum hM.le
    have h2 : M * (∑ n ∈ Finset.Icc 2 k, tdH σ A n) + (M+1) * (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n)
        = M * ((∑ n ∈ Finset.Icc 2 k, tdH σ A n) + (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n))
          + (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n) := by ring
    linarith [h1, hSk'_le, h2]
  calc (∑ n ∈ Finset.Icc 2 N, tdDg M n * tdH σ A n)
      ≤ ∑ n ∈ Finset.Icc 2 N, (tdG M n + 1) * tdH σ A n := hstep1
    _ = (∑ n ∈ Finset.Icc 2 k, (tdG M n + 1) * tdH σ A n)
          + (∑ n ∈ Finset.Icc (k+1) N, (tdG M n + 1) * tdH σ A n) := hsum_split _
    _ ≤ (M * (∑ n ∈ Finset.Icc 2 k, tdH σ A n)
            - (∑ n ∈ Finset.Icc 2 k, (M - Real.log (n:ℝ) - 1) * tdH σ A n))
          + (M+1) * (∑ n ∈ Finset.Icc (k+1) N, tdH σ A n) := by
        rw [hstep3]; linarith [hstep4]
    _ ≤ M * (Real.Gamma σ * A^σ)
          - (∑ n ∈ Finset.Icc 2 k, (M - Real.log (n:ℝ) - 1) * tdH σ A n)
          + (Real.Gamma σ * A^σ) := by linarith [hstep6]

end Work.LinnikAreas.Density4
