import Mathlib
import Submission.Work.BMF.liouville.vkbl_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Weyl shift for `ESb`

`Work.BMF.liouville.ESb_shift`: the block sum `Σ_{⌊N⌋<n≤⌊R⌋}(n+u)^{-it}` is bounded by the
average of the moduli of the "relative" sums `Trel M n u t = Σ_{m≤M}(1+m/(n+u))^{-it}`, plus the
shift error `2M`.
-/

open Finset

namespace Work.BMF.liouville

noncomputable section

lemma Ioc_eq_Ico_succ' (a b : ℕ) : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
  ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega

/-- Telescoping sum over `Ioc`. -/
lemma sum_Ioc_sub_eq (g : ℕ → ℂ) (a b i : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (g (n + i + 1) - g (n + i)) = g (b + i + 1) - g (a + i + 1) := by
  rw [Ioc_eq_Ico_succ', Finset.sum_Ico_eq_sum_range]
  have h1 : b + 1 - (a + 1) = b - a := by omega
  rw [h1]
  have h3 : ∀ j : ℕ, g (a + 1 + j + i + 1) - g (a + 1 + j + i)
      = g (a + i + 1 + (j + 1)) - g (a + i + 1 + j) := by
    intro j
    rw [show a + 1 + j + i + 1 = a + i + 1 + (j + 1) by omega,
        show a + 1 + j + i = a + i + 1 + j by omega]
  simp only [h3]
  rw [Finset.sum_range_sub (fun j => g (a + i + 1 + j)) (b - a)]
  rw [show a + i + 1 + (b - a) = b + i + 1 by omega, show a + i + 1 + 0 = a + i + 1 by omega]

theorem ESb_shift (M : ℕ) (hM : 1 ≤ M) (N R u t : ℝ) (hu : 0 < u) :
    ‖Work.BMF.zpt.ESb N R u t‖ ≤
      (1 / (M : ℝ)) * ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ‖Trel M n u t‖ + 2 * (M : ℝ) := by
  set N₀ : ℕ := ⌊N⌋₊ with hN₀
  set R₀ : ℕ := ⌊R⌋₊ with hR₀
  set f : ℕ → ℂ := fun k => ((((k : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) with hf
  have hfpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + u := by
    intro k; have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
  have hfnorm : ∀ k : ℕ, ‖f k‖ = 1 := by
    intro k; rw [hf]; exact norm_cpow_eq_one _ _ (hfpos k)
  -- Step A: `f n * relT u t n m = f (n+m)`
  have hfrel : ∀ n m : ℕ, f n * relT u t n m = f (n + m) := by
    intro n m
    have h1 : f n = Work.BMF.eC (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u)) := by
      rw [hf]; exact cpow_eq_eC _ _ (hfpos n)
    have h2 : f (n + m) = Work.BMF.eC
        (-(t / (2 * Real.pi)) * Real.log (((n + m : ℕ) : ℝ) + u)) := by
      rw [hf]; exact cpow_eq_eC _ _ (hfpos (n + m))
    have h3 : (1 : ℝ) + (m : ℝ) / ((n : ℝ) + u) = (((n + m : ℕ) : ℝ) + u) / ((n : ℝ) + u) := by
      push_cast; field_simp; ring
    have hlog : Real.log ((((n + m : ℕ) : ℝ) + u))
        = Real.log ((n : ℝ) + u) + Real.log ((((n + m : ℕ) : ℝ) + u) / ((n : ℝ) + u)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [h1, h2, relT, h3, ← Work.BMF.zpt.eC_add, hlog]
    ring
  -- Step B: the shifted sums
  set Sf : ℕ → ℂ := fun m => ∑ n ∈ Finset.Ioc N₀ R₀, f (n + m) with hSf
  have hS0 : Sf 0 = Work.BMF.zpt.ESb N R u t := by
    rw [hSf]
    simp only [Nat.add_zero]
    unfold Work.BMF.zpt.ESb
    rw [hf, hN₀, hR₀]
  -- Step C: `Σ_m Sf m = Σ_n f n * Trel M n u t`
  have hC : ∑ m ∈ Finset.Icc 1 M, Sf m
      = ∑ n ∈ Finset.Ioc N₀ R₀, f n * Trel M n u t := by
    rw [hSf]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold Trel
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact (hfrel n m).symm
  -- Step D: `‖Sf m - Sf 0‖ ≤ 2m`
  have hD : ∀ m : ℕ, ‖Sf m - Sf 0‖ ≤ 2 * (m : ℝ) := by
    intro m
    rcases le_or_gt N₀ R₀ with hNR | hNR
    · have h1 : Sf m - Sf 0 = ∑ n ∈ Finset.Ioc N₀ R₀, (f (n + m) - f n) := by
        rw [hSf]; simp only [Nat.add_zero]
        rw [Finset.sum_sub_distrib]
      have h2 : ∀ n : ℕ, f (n + m) - f n
          = ∑ i ∈ Finset.range m, (f (n + i + 1) - f (n + i)) := by
        intro n
        have h := Finset.sum_range_sub (fun i => f (n + i)) m
        have h' : ∑ i ∈ Finset.range m, (f (n + i + 1) - f (n + i)) = f (n + m) - f n := by
          simpa only [Nat.add_succ, Nat.add_zero] using h
        rw [h']
      have htel : Sf m - Sf 0
          = ∑ i ∈ Finset.range m, (f (R₀ + i + 1) - f (N₀ + i + 1)) := by
        rw [h1]
        simp only [h2]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_Ioc_sub_eq f N₀ R₀ i hNR]
      rw [htel]
      calc ‖∑ i ∈ Finset.range m, (f (R₀ + i + 1) - f (N₀ + i + 1))‖
          ≤ ∑ i ∈ Finset.range m, ‖f (R₀ + i + 1) - f (N₀ + i + 1)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range m, (2 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            calc ‖f (R₀ + i + 1) - f (N₀ + i + 1)‖
                ≤ ‖f (R₀ + i + 1)‖ + ‖f (N₀ + i + 1)‖ := norm_sub_le _ _
              _ = 2 := by rw [hfnorm, hfnorm]; norm_num
        _ = 2 * (m : ℝ) := by simp [mul_comm]
    · have hempty : Finset.Ioc N₀ R₀ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx; rw [Finset.mem_Ioc] at hx; omega
      have hz : Sf m = 0 ∧ Sf 0 = 0 := by
        constructor <;> · rw [hSf]; simp [hempty]
      rw [hz.1, hz.2]; simp
  -- Step E: combine
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsum0 : ∑ _m ∈ Finset.Icc 1 M, Sf 0 = (M : ℂ) * Sf 0 := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
    simp
  have hstep : (M : ℝ) * ‖Sf 0‖ ≤ (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ) ^ 2 := by
    have hnormM : ‖(M : ℂ) * Sf 0‖ = (M : ℝ) * ‖Sf 0‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← hnormM]
    have hsplit : (M : ℂ) * Sf 0
        = (∑ m ∈ Finset.Icc 1 M, Sf m) - ∑ m ∈ Finset.Icc 1 M, (Sf m - Sf 0) := by
      rw [Finset.sum_sub_distrib, ← hsum0]
      ring
    rw [hsplit]
    have hCb : ‖∑ m ∈ Finset.Icc 1 M, Sf m‖ ≤ ∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖ := by
      rw [hC]
      calc ‖∑ n ∈ Finset.Ioc N₀ R₀, f n * Trel M n u t‖
          ≤ ∑ n ∈ Finset.Ioc N₀ R₀, ‖f n * Trel M n u t‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖ := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [norm_mul, hfnorm, one_mul]
    calc ‖(∑ m ∈ Finset.Icc 1 M, Sf m) - ∑ m ∈ Finset.Icc 1 M, (Sf m - Sf 0)‖
        ≤ ‖∑ m ∈ Finset.Icc 1 M, Sf m‖ + ‖∑ m ∈ Finset.Icc 1 M, (Sf m - Sf 0)‖ := norm_sub_le _ _
      _ ≤ ‖∑ m ∈ Finset.Icc 1 M, Sf m‖ + ∑ m ∈ Finset.Icc 1 M, ‖Sf m - Sf 0‖ :=
          add_le_add le_rfl (norm_sum_le _ _)
      _ ≤ ‖∑ m ∈ Finset.Icc 1 M, Sf m‖ + ∑ m ∈ Finset.Icc 1 M, (2 * (M : ℝ)) := by
          refine add_le_add le_rfl (Finset.sum_le_sum fun m hm => ?_)
          calc ‖Sf m - Sf 0‖ ≤ 2 * (m : ℝ) := hD m
            _ ≤ 2 * (M : ℝ) := by
                have : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
                linarith
      _ = ‖∑ m ∈ Finset.Icc 1 M, Sf m‖ + 2 * (M : ℝ) ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
          simp only [nsmul_eq_mul]; ring
      _ ≤ (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ) ^ 2 :=
          add_le_add hCb le_rfl
  have hfin : ‖Sf 0‖ ≤ (1 / (M : ℝ)) * (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ) := by
    have h3 : (M : ℝ) * ((1 / (M : ℝ)) * (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ))
        = (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ) ^ 2 := by
      rw [mul_add, ← mul_assoc, mul_one_div_cancel (ne_of_gt hMpos), one_mul]; ring
    have h4 : (M : ℝ) * ‖Sf 0‖
        ≤ (M : ℝ) * ((1 / (M : ℝ)) * (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ)) := by
      rw [h3]; exact hstep
    exact le_of_mul_le_mul_left h4 hMpos
  rw [← hS0]
  calc ‖Sf 0‖
      ≤ (1 / (M : ℝ)) * (∑ n ∈ Finset.Ioc N₀ R₀, ‖Trel M n u t‖) + 2 * (M : ℝ) := hfin
    _ = (1 / (M : ℝ)) * ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ‖Trel M n u t‖ + 2 * (M : ℝ) := by
        rw [hN₀, hR₀]

end

end Work.BMF.liouville
