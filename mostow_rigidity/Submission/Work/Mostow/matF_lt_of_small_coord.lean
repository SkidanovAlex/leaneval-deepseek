import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

namespace Work.Mostow

noncomputable section

set_option linter.unusedVariables false

open Finset

/-- `matC n = (√n / (n-1))^n` is positive as soon as `n ≥ 2`. -/
lemma matC_pos {n : ℕ} (hn : 2 ≤ n) : 0 < matC n := by
  unfold matC
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  exact pow_pos (div_pos (Real.sqrt_pos.mpr hn0) (by linarith)) n

/-- Splitting off the coordinate `j` in `matF`. -/
lemma matF_eq_succAbove {m : ℕ} (x : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (hj : x j ≠ 1) :
    matF x = (Real.sqrt (x j) / (1 - x j)) *
      ((∏ i, Real.sqrt (x (j.succAbove i))) / (∏ i, (1 - x (j.succAbove i)))) := by
  simp only [matF]
  rw [Fin.prod_univ_succAbove _ j, Fin.prod_univ_succAbove _ j]
  have h : (1 : ℝ) - x j ≠ 0 := by intro hz; exact hj (by linarith)
  field_simp

/-- The main product estimate: if `z = s • y` with `0 < s ≤ 1`, then the `z`-product is
bounded by `(√s)^m` times the `matF` of `y`. -/
lemma prod_sqrt_div_prod_le {m : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {z y : Fin m → ℝ} (hz : ∀ i, z i = s * y i) (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, y i < 1) :
    (∏ i, Real.sqrt (z i)) / (∏ i, (1 - z i)) ≤ (Real.sqrt s) ^ m * matF y := by
  have hsnn : 0 ≤ s := le_of_lt hs0
  have hnum : ∏ i, Real.sqrt (z i) = (Real.sqrt s) ^ m * ∏ i, Real.sqrt (y i) := by
    rw [Finset.prod_congr rfl (g := fun i => Real.sqrt s * Real.sqrt (y i)) (by
      intro i _; rw [hz i, Real.sqrt_mul hsnn])]
    rw [Finset.prod_mul_distrib]
    simp
  have hden : ∏ i, (1 - y i) ≤ ∏ i, (1 - z i) := by
    apply Finset.prod_le_prod₀ (fun i _ => by linarith [hy1 i])
    intro i _
    rw [hz i]
    nlinarith [hy0 i, hs1]
  have hdenpos : 0 < ∏ i, (1 - y i) := Finset.prod_pos (fun i _ => by linarith [hy1 i])
  have hnum_nn : 0 ≤ (Real.sqrt s) ^ m * ∏ i, Real.sqrt (y i) :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg s) m)
      (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
  rw [hnum, matF]
  exact (div_le_div_of_nonneg_left hnum_nn hdenpos hden).trans_eq (by ring)

theorem matF_lt_of_small_coord {n : ℕ} (hn : 4 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {C : ℝ} (hC : 0 < C)
    (hprev : ∀ (y : Fin (n - 1) → ℝ), (∀ i, 0 ≤ y i) → (∀ i, y i < 1) →
      (∑ i, y i) = 1 → matF y ≤ C)
    (hδC : Real.sqrt δ * C < matC n)
    (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) (hsum : ∑ i, x i = 1)
    (hsmall : ∃ i, x i ≤ δ) : matF x < matC n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 3 ≤ m := by omega
  have hmatC : 0 < matC (m + 1) := matC_pos (by omega)
  by_cases hzero : ∃ k, x k = 0
  · -- a vanishing coordinate kills the whole product
    obtain ⟨k, hk⟩ := hzero
    have hprod : (∏ i, Real.sqrt (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, Real.sqrt_zero])
    have h0 : matF x = 0 := by
      simp only [matF]
      rw [hprod, zero_div]
    rw [h0]; exact hmatC
  · have hxpos : ∀ k, 0 < x k := fun k =>
      lt_of_le_of_ne (hx0 k) (Ne.symm (fun h => hzero ⟨k, h⟩))
    obtain ⟨j, hj⟩ := hsmall
    set s : ℝ := 1 - x j with hs_def
    have hs0 : 0 < s := by rw [hs_def]; linarith [hx1 j]
    have hs1 : s ≤ 1 := by rw [hs_def]; linarith [hx0 j]
    set z : Fin m → ℝ := fun i => x (j.succAbove i) with hz_def
    have hzpos : ∀ i, 0 < z i := by
      intro i
      simp only [hz_def]
      exact lt_of_le_of_ne (hx0 _) (Ne.symm (fun h => hzero ⟨_, h⟩))
    have hsum_split : ∑ i : Fin m, z i = s := by
      have h1 := Fin.sum_univ_succAbove x j
      simp only [hs_def, hz_def]
      linarith [hsum, h1]
    set y : Fin m → ℝ := fun i => z i / s with hy_def
    have hy0 : ∀ i, 0 ≤ y i := by
      intro i
      simp only [hy_def]
      exact div_nonneg (le_of_lt (hzpos i)) (le_of_lt hs0)
    have hy_sum : ∑ i, y i = 1 := by
      simp only [hy_def]
      rw [← Finset.sum_div, hsum_split, div_self (ne_of_gt hs0)]
    have hzc : ∀ i, z i = s * y i := by
      intro i
      simp only [hy_def]
      field_simp
    have hy1 : ∀ i, y i < 1 := by
      intro i
      have hzi_lt : z i < s := by
        have hne : (Finset.univ.erase i : Finset (Fin m)).Nonempty := by
          obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin m)
            (by simp only [Fintype.card_fin]; omega) i
          exact ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩
        have hrest : 0 < ∑ k ∈ (Finset.univ.erase i : Finset (Fin m)), z k :=
          Finset.sum_pos (fun k _ => hzpos k) hne
        have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) z (Finset.mem_univ i)
        rw [← hsum_split]
        linarith
      simp only [hy_def]
      rw [div_lt_one hs0]
      linarith
    have hymatF : matF y ≤ C := hprev y hy0 hy1 hy_sum
    have hy_nn : 0 ≤ matF y := by
      simp only [matF]
      exact div_nonneg (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
        (le_of_lt (Finset.prod_pos (fun i _ => by linarith [hy1 i])))
    have hA := prod_sqrt_div_prod_le hs0 hs1 hzc hy0 hy1
    have hsplit0 := matF_eq_succAbove x j (ne_of_lt (hx1 j))
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt (le_of_lt hs0)
    have hsqrt_le_one : Real.sqrt s ≤ 1 := by
      have h := Real.sqrt_le_sqrt hs1
      rwa [Real.sqrt_one] at h
    have hpow : Real.sqrt s ^ m = s * Real.sqrt s ^ (m - 2) := by
      conv_lhs => rw [show m = (m - 2) + 2 by omega]
      rw [pow_add, hsq]
      ring
    have step1 : matF x ≤ (Real.sqrt (x j) / s) * ((Real.sqrt s) ^ m * matF y) := by
      rw [hsplit0, ← hs_def]
      exact mul_le_mul_of_nonneg_left hA (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hs0))
    have step2 : (Real.sqrt (x j) / s) * ((Real.sqrt s) ^ m * matF y)
        = (Real.sqrt (x j) * Real.sqrt s ^ (m - 2)) * matF y := by
      rw [hpow]; field_simp
    have step3 : (Real.sqrt (x j) * Real.sqrt s ^ (m - 2)) * matF y ≤ Real.sqrt δ * C := by
      have hcoef : Real.sqrt (x j) * Real.sqrt s ^ (m - 2) ≤ Real.sqrt δ := by
        have h1 : Real.sqrt (x j) ≤ Real.sqrt δ := Real.sqrt_le_sqrt hj
        have h2 : Real.sqrt s ^ (m - 2) ≤ 1 :=
          pow_le_one₀ (Real.sqrt_nonneg s) hsqrt_le_one
        calc Real.sqrt (x j) * Real.sqrt s ^ (m - 2) ≤ Real.sqrt δ * 1 :=
              mul_le_mul h1 h2 (pow_nonneg (Real.sqrt_nonneg s) _) (Real.sqrt_nonneg δ)
          _ = Real.sqrt δ := by ring
      exact mul_le_mul hcoef hymatF hy_nn (Real.sqrt_nonneg δ)
    calc matF x ≤ (Real.sqrt (x j) * Real.sqrt s ^ (m - 2)) * matF y :=
          le_trans step1 (le_of_eq step2)
      _ ≤ Real.sqrt δ * C := step3
      _ < matC (m + 1) := hδC

end

end Work.Mostow
