import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

namespace Work.LinnikAreas.Density4

theorem thetaDiag_Q1_lower (M σ A : ℝ) (hM : 2 ≤ M) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hA : Real.exp M ≤ A) :
    Work.LinnikAreas.Density4.tdQ σ A M - Real.exp 1 * Real.exp (σ * M) ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1) * Work.LinnikAreas.Density4.tdH σ A n := by
  have hA_pos : 0 < A := lt_of_lt_of_le (Real.exp_pos M) hA
  rw [tdQ]
  set N₁ : ℕ := ⌊Real.exp (M-1)⌋₊ with hN₁
  set N₂ : ℕ := ⌊Real.exp M⌋₊ with hN₂
  have hN12 : N₁ ≤ N₂ := by
    rw [hN₁, hN₂]
    exact Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hsub : Finset.Icc 2 N₁ ⊆ Finset.Icc 2 N₂ := Finset.Icc_subset_Icc le_rfl hN12
  have hsdiff := Finset.sum_sdiff (s₁ := Finset.Icc 2 N₁) (s₂ := Finset.Icc 2 N₂)
      (f := fun n => (M - Real.log (n:ℝ) - 1) * tdH σ A n) hsub
  have hterm : ∀ n ∈ Finset.Icc 2 N₂ \ Finset.Icc 2 N₁,
      -(Real.exp ((σ-1)*(M-1))) ≤ (M - Real.log (n:ℝ) - 1) * tdH σ A n := by
    intro n hn
    have hmem : n ∈ Finset.Icc 2 N₂ := (Finset.mem_sdiff.mp hn).1
    have hnN₁ : n ∉ Finset.Icc 2 N₁ := (Finset.mem_sdiff.mp hn).2
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hmem).1
    have hnN₂ : n ≤ N₂ := (Finset.mem_Icc.mp hmem).2
    have hnN₁' : N₁ < n := by
      by_contra h
      exact hnN₁ (Finset.mem_Icc.mpr ⟨hn2, not_lt.mp h⟩)
    have hnpos : 0 < (n:ℝ) := by
      have hn0 : 0 < n := by omega
      exact_mod_cast hn0
    have hlog : Real.log (n:ℝ) ≤ M := by
      rw [Real.log_le_iff_le_exp hnpos]
      have hN₂le : (N₂:ℝ) ≤ Real.exp M := by
        rw [hN₂]; exact Nat.floor_le (Real.exp_pos M).le
      exact le_trans (by exact_mod_cast hnN₂) hN₂le
    have ht_nonneg : 0 ≤ tdH σ A n := by
      rw [tdH]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _) (Real.exp_nonneg _)
    have hneed : Real.exp (M-1) ≤ (n:ℝ) := by
      have h1 : Real.exp (M-1) < (N₁:ℝ) + 1 := by
        rw [hN₁]; exact Nat.lt_floor_add_one _
      have h2 : (N₁:ℝ) + 1 ≤ (n:ℝ) := by
        have : N₁ + 1 ≤ n := by omega
        exact_mod_cast this
      linarith
    have ht_le : tdH σ A n ≤ Real.exp ((σ-1)*(M-1)) := by
      rw [tdH]
      have hσm1 : σ - 1 ≤ 0 := by linarith
      have hrpow : (n:ℝ)^(σ-1) ≤ Real.exp ((σ-1)*(M-1)) := by
        calc (n:ℝ)^(σ-1) ≤ (Real.exp (M-1))^(σ-1) :=
              Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hneed hσm1
          _ = Real.exp ((M-1)*(σ-1)) := (Real.exp_mul _ _).symm
          _ = Real.exp ((σ-1)*(M-1)) := by congr 1; ring
      have hexp_le : Real.exp (-(n:ℝ)/A) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hA_pos)
      calc (n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A)
            ≤ Real.exp ((σ-1)*(M-1)) * 1 :=
              mul_le_mul hrpow hexp_le (Real.exp_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp ((σ-1)*(M-1)) := by ring
    have h1 : (-1 : ℝ) * tdH σ A n ≤ (M - Real.log (n:ℝ) - 1) * tdH σ A n :=
      mul_le_mul_of_nonneg_right (by linarith) ht_nonneg
    have h2 : -(Real.exp ((σ-1)*(M-1))) ≤ (-1 : ℝ) * tdH σ A n := by linarith
    linarith
  have hsum_lower : ∑ n ∈ Finset.Icc 2 N₂ \ Finset.Icc 2 N₁, -(Real.exp ((σ-1)*(M-1)))
      ≤ ∑ n ∈ Finset.Icc 2 N₂ \ Finset.Icc 2 N₁, (M - Real.log (n:ℝ) - 1) * tdH σ A n :=
    Finset.sum_le_sum hterm
  have hconst_sum : ∑ n ∈ Finset.Icc 2 N₂ \ Finset.Icc 2 N₁, -(Real.exp ((σ-1)*(M-1)))
      = -((Finset.Icc 2 N₂ \ Finset.Icc 2 N₁).card : ℝ) * Real.exp ((σ-1)*(M-1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : ((Finset.Icc 2 N₂ \ Finset.Icc 2 N₁).card : ℝ) * Real.exp ((σ-1)*(M-1))
      ≤ Real.exp 1 * Real.exp (σ*M) := by
    have hcard_le : (Finset.Icc 2 N₂ \ Finset.Icc 2 N₁).card ≤ N₂ := by
      have hsub' : Finset.Icc 2 N₂ \ Finset.Icc 2 N₁ ⊆ Finset.Icc 1 N₂ := by
        intro n hn
        rw [Finset.mem_sdiff, Finset.mem_Icc] at hn
        rw [Finset.mem_Icc]
        exact ⟨by omega, hn.1.2⟩
      calc (Finset.Icc 2 N₂ \ Finset.Icc 2 N₁).card ≤ (Finset.Icc 1 N₂).card :=
            Finset.card_le_card hsub'
        _ = N₂ := by rw [Nat.card_Icc]; omega
    have hN₂le : (N₂:ℝ) ≤ Real.exp M := by
      rw [hN₂]; exact Nat.floor_le (Real.exp_pos M).le
    have h1 : ((Finset.Icc 2 N₂ \ Finset.Icc 2 N₁).card : ℝ) ≤ (N₂:ℝ) := by
      exact_mod_cast hcard_le
    have h3 : (N₂:ℝ) * Real.exp ((σ-1)*(M-1)) ≤ Real.exp M * Real.exp ((σ-1)*(M-1)) :=
      mul_le_mul_of_nonneg_right hN₂le (Real.exp_nonneg _)
    have h4 : Real.exp M * Real.exp ((σ-1)*(M-1)) = Real.exp (σ*M - σ + 1) := by
      rw [← Real.exp_add]; congr 1; ring
    have h5 : σ*M - σ + 1 ≤ σ*M + 1 := by linarith
    have h6 : Real.exp (σ*M + 1) = Real.exp 1 * Real.exp (σ*M) := by
      rw [Real.exp_add]; ring
    calc ((Finset.Icc 2 N₂ \ Finset.Icc 2 N₁).card : ℝ) * Real.exp ((σ-1)*(M-1))
        ≤ (N₂:ℝ) * Real.exp ((σ-1)*(M-1)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ ≤ Real.exp M * Real.exp ((σ-1)*(M-1)) := h3
      _ = Real.exp (σ*M - σ + 1) := h4
      _ ≤ Real.exp (σ*M + 1) := Real.exp_le_exp.mpr h5
      _ = Real.exp 1 * Real.exp (σ*M) := h6
  have hbound : -(Real.exp 1 * Real.exp (σ*M)) ≤
      ∑ n ∈ Finset.Icc 2 N₂ \ Finset.Icc 2 N₁, (M - Real.log (n:ℝ) - 1) * tdH σ A n := by
    have h := hsum_lower
    rw [hconst_sum] at h
    linarith
  rw [← hsdiff]
  linarith

end Work.LinnikAreas.Density4
