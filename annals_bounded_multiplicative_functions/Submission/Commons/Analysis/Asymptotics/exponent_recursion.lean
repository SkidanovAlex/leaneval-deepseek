import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Asymptotics

open Finset

private lemma sum_identity {k : ℕ} (hk : 2 ≤ k) (A : ℕ → ℝ) :
    ∑ l ∈ Finset.Ico 1 k,
      ((1 / (l : ℝ)) * A (k - l) + (((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1)) * A (l - 1) - A l)
    = (((k - 1 : ℕ) : ℝ) / k) * A 0 := by
  have hk1 : 1 ≤ k := by omega
  -- Step 1: split into three sums and reorder.
  set E1 := ∑ l ∈ Finset.Ico 1 k, (1 / (l : ℝ)) * A (k - l) with hE1
  set E2 := ∑ l ∈ Finset.Ico 1 k, (((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1)) * A (l - 1) with hE2
  set E3 := ∑ l ∈ Finset.Ico 1 k, A l with hE3
  have hmain : (∑ l ∈ Finset.Ico 1 k,
      ((1 / (l : ℝ)) * A (k - l) + (((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1)) * A (l - 1) - A l))
      = (E1 - E3) + E2 := by
    rw [hE1, hE2, hE3, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  -- Step 2: reflect E1.
  have hE1' : E1 = ∑ m ∈ Finset.Ico 1 k, (1 / ((k - m : ℕ) : ℝ)) * A m := by
    rw [hE1]
    refine Finset.sum_bij (fun a _ => k - a) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a1 ha1 a2 ha2 heq; simp only [Finset.mem_Ico] at ha1 ha2; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb
      exact ⟨k - b, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro a ha; simp only [Finset.mem_Ico] at ha
      have h : k - (k - a) = a := by omega
      rw [h]
  -- Step 3: shift E2.
  have hE2' : E2 = ∑ m ∈ Finset.Ico 0 (k - 1), (((k - 1 - m : ℕ) : ℝ) / ((k - m : ℕ) : ℝ)) * A m := by
    rw [hE2]
    refine Finset.sum_bij (fun a _ => a - 1) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a1 ha1 a2 ha2 heq; simp only [Finset.mem_Ico] at ha1 ha2; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb
      exact ⟨b + 1, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro a ha; simp only [Finset.mem_Ico] at ha
      have h1 : k - 1 - (a - 1) = k - a := by omega
      have h2 : k - (a - 1) = k - a + 1 := by omega
      rw [h1, h2]; push_cast; ring
  -- Step 4: combine reflected E1 with -E3.
  have hcomb : (∑ m ∈ Finset.Ico 1 k, (1 / ((k - m : ℕ) : ℝ)) * A m) - E3
      = ∑ m ∈ Finset.Ico 1 k, ((1 / ((k - m : ℕ) : ℝ)) - 1) * A m := by
    rw [hE3, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm; ring
  -- Step 5: split the d-sum at the top.
  have htop : (∑ m ∈ Finset.Ico 1 k, ((1 / ((k - m : ℕ) : ℝ)) - 1) * A m)
      = (∑ m ∈ Finset.Ico 1 (k - 1), ((1 / ((k - m : ℕ) : ℝ)) - 1) * A m)
        + ((1 / ((k - (k - 1) : ℕ) : ℝ)) - 1) * A (k - 1) := by
    have h := Finset.sum_Ico_succ_top (a := 1) (b := k - 1) (by omega : 1 ≤ k - 1)
      (fun m => ((1 / ((k - m : ℕ) : ℝ)) - 1) * A m)
    rw [show (k - 1) + 1 = k from by omega] at h
    exact h
  -- Step 6: split the c-sum at the bottom.
  have hbot : (∑ m ∈ Finset.Ico 0 (k - 1), (((k - 1 - m : ℕ) : ℝ) / ((k - m : ℕ) : ℝ)) * A m)
      = (((k - 1 - 0 : ℕ) : ℝ) / ((k - 0 : ℕ) : ℝ)) * A 0
        + ∑ m ∈ Finset.Ico 1 (k - 1), (((k - 1 - m : ℕ) : ℝ) / ((k - m : ℕ) : ℝ)) * A m := by
    have h := Finset.sum_Ico_consecutive
      (fun m => (((k - 1 - m : ℕ) : ℝ) / ((k - m : ℕ) : ℝ)) * A m)
      (by omega : 0 ≤ 1) (by omega : 1 ≤ k - 1)
    have h01 : ∑ m ∈ Finset.Ico 0 1, (((k - 1 - m : ℕ) : ℝ) / ((k - m : ℕ) : ℝ)) * A m
        = (((k - 1 - 0 : ℕ) : ℝ) / ((k - 0 : ℕ) : ℝ)) * A 0 := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
    rw [← h, h01]
  -- Assemble
  rw [hmain, hE1', hE2', hcomb, htop, hbot]
  set Psum : ℝ := ∑ m ∈ Finset.Ico 1 (k - 1), ((1 / ((k - m : ℕ) : ℝ)) - 1) * A m with hPsum
  set Dterm : ℝ := ((1 / ((k - (k - 1) : ℕ) : ℝ)) - 1) * A (k - 1) with hDterm
  set Cterm : ℝ := (((k - 1 - 0 : ℕ) : ℝ) / ((k - 0 : ℕ) : ℝ)) * A 0 with hCterm
  set Qsum : ℝ := ∑ m ∈ Finset.Ico 1 (k - 1), (((k - 1 - m : ℕ) : ℝ) / ((k - m : ℕ) : ℝ)) * A m with hQsum
  have hD : Dterm = 0 := by
    rw [hDterm]
    have h1 : (k - (k - 1) : ℕ) = 1 := by omega
    rw [h1]; norm_num
  have hPQ : Psum + Qsum = 0 := by
    rw [hPsum, hQsum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_Ico] at hm
    have hx : ((k - m : ℕ) : ℝ) ≠ 0 := by
      have : (k - m : ℕ) ≠ 0 := by omega
      exact_mod_cast this
    have hy : ((k - 1 - m : ℕ) : ℝ) = ((k - m : ℕ) : ℝ) - 1 := by
      have hge : 1 ≤ k - m := by omega
      have hthis : k - 1 - m = k - m - 1 := by omega
      rw [hthis, Nat.cast_sub hge]
      norm_num
    rw [hy, ← add_mul]
    have hsum : (1 / ((k - m : ℕ) : ℝ) - 1) + (((k - m : ℕ) : ℝ) - 1) / ((k - m : ℕ) : ℝ) = 0 := by
      field_simp
      ring
    rw [hsum, zero_mul]
  have hC : Cterm = (((k - 1 : ℕ) : ℝ) / k) * A 0 := by
    rw [hCterm]
    have h1 : k - 1 - 0 = k - 1 := by omega
    have h2 : k - 0 = k := by omega
    rw [h1, h2]
  linear_combination hPQ + hD + hC

theorem exponent_recursion {k : ℕ} (hk : 2 ≤ k) (A : ℕ → ℝ) (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k - 1 → (1 / (l : ℝ)) * A (k - l) + (((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1)) * A (l - 1) ≤ A l) : A 0 ≤ 0 := by
  have hle : ∑ l ∈ Finset.Ico 1 k,
      ((1 / (l : ℝ)) * A (k - l) + (((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1)) * A (l - 1) - A l) ≤ 0 := by
    apply Finset.sum_nonpos
    intro l hl
    simp only [Finset.mem_Ico] at hl
    have := hrec l hl.1 (by omega)
    linarith
  rw [sum_identity hk A] at hle
  have hnum : (0:ℝ) < ((k - 1 : ℕ) : ℝ) := by
    have : (0:ℕ) < k - 1 := by omega
    exact_mod_cast this
  have hden : (0:ℝ) < (k : ℝ) := by
    have : (0:ℕ) < k := by omega
    exact_mod_cast this
  have hpos : (0:ℝ) < ((k - 1 : ℕ) : ℝ) / k := div_pos hnum hden
  by_contra hcon
  have hA0 : 0 < A 0 := not_le.mp hcon
  nlinarith [hle, hpos, hA0]

end Commons.Analysis.Asymptotics
