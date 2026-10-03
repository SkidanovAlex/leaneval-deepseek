import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.smallCInner2EpsAux.hypArithEps
import Submission.Work.FIArea7.smallCInner2EpsAux.hypBlock_le_eps
import Submission.Work.FIArea7.exists_separating_function

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The hyperbola (Type II) form of *FI* Proposition 23.1, with power loss.** -/
theorem hyperbolaBilinEps (h31 : Work.FIArea7.Prop231) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (c0 M N u : ℕ) (α β : ℕ → ℂ),
        1 ≤ c0 →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1) → (∀ n ∈ Finset.Icc 1 N, ‖β n‖ ≤ 1) →
        ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * (m * n)) else 0)‖
          ≤ C * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
              * ((u : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ A
              * (((u : ℝ) + (c0 : ℝ) + 2) ^ ε) := by
  intro ε hε
  obtain ⟨C1, hC1, hmain⟩ := h31 ε hε
  refine ⟨C1 * (2 ^ ((11 : ℝ) / 12) * (2 ^ ε) * 10), 2, ?_, by norm_num, ?_⟩
  · exact mul_pos hC1 (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num))
  · intro chi k c0 M N u α β hc0 hchi hchi_mul hα hβ
    have hτnn : (0 : ℝ) ≤ ((c0.divisors.card : ℕ) : ℝ) := by positivity
    have hRHSnn : 0 ≤ C1 * (2 ^ ((11 : ℝ) / 12) * (2 ^ ε) * 10)
        * (((c0.divisors.card : ℕ) : ℝ))
        * (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) * ((u : ℝ) ^ ((11 : ℝ) / 12))
        * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ) * (((u : ℝ) + (c0 : ℝ) + 2) ^ ε) := by
      have h1 : (0 : ℝ) ≤ 2 ^ ((11 : ℝ) / 12) * (2 ^ ε) * 10 :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)) (by norm_num)
      have h2 : (0 : ℝ) ≤ ((M : ℝ) + N) ^ ((1 : ℝ) / 12) := Real.rpow_nonneg (by positivity) _
      have h3 : (0 : ℝ) ≤ (u : ℝ) ^ ((11 : ℝ) / 12) := Real.rpow_nonneg (by positivity) _
      have h4 : (0 : ℝ) ≤ ((u : ℝ) + (c0 : ℝ) + 2) ^ ε := Real.rpow_nonneg (by positivity) _
      have h5 : (0 : ℝ) ≤ (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ) :=
        Real.rpow_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (u : ℝ) by positivity])) _
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1)
        h1) hτnn) h2) h3) h5) h4
    by_cases hM0 : M = 0
    · have hS : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n
              * quadEigen (grossenChar chi k) (c0 * (m * n)) else 0)) = 0 := by
        rw [hM0]; simp
      rw [hS, norm_zero]; exact hRHSnn
    by_cases hN0 : N = 0
    · have hS : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n
              * quadEigen (grossenChar chi k) (c0 * (m * n)) else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro m hm
        rw [hN0]; simp
      rw [hS, norm_zero]; exact hRHSnn
    by_cases hu0 : u = 0
    · have hS : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n
              * quadEigen (grossenChar chi k) (c0 * (m * n)) else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro m hm
        apply Finset.sum_eq_zero; intro n hn
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hmn : 1 ≤ m * n := by
          have : 0 < m * n := Nat.mul_pos (by omega) (by omega)
          omega
        rw [hu0, if_neg (by omega : ¬ m * n ≤ 0)]
      rw [hS, norm_zero]; exact hRHSnn
    have hM : 1 ≤ M := by omega
    have hN : 1 ≤ N := by omega
    have hu : 1 ≤ u := by omega
    obtain ⟨h, hL1, hspec⟩ := exists_separating_function (u : ℝ) (by exact_mod_cast hu)
    have hbound : ∀ (Ma Ca : ℕ) (γ δ : ℕ → ℂ), 1 ≤ Ma → 1 ≤ Ca →
        (∀ m ∈ Finset.Icc 1 Ma, ‖γ m‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 Ca, ‖δ n‖ ≤ 1) →
        ‖LBilin Ma Ca c0 (grossenChar chi k) γ δ‖
          ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * ((Ma : ℝ) + Ca) ^ ((1 : ℝ) / 12)
              * ((Ma : ℝ) * Ca) ^ ((11 : ℝ) / 12)
              * (((Ma : ℝ) * Ca + (c0 : ℝ) + 2) ^ ε) := by
      intro Ma Ca γ δ hMa hCa hγ hδ
      exact (hmain Ma Ca c0 1 k chi γ δ hc0 hMa hCa le_rfl hchi hchi_mul hγ hδ).1
    rw [show (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ u then α m * β n
            * quadEigen (grossenChar chi k) (c0 * (m * n)) else 0))
        = (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ u then α m * β n
            * quadEigen (grossenChar chi k) (c0 * m * n) else 0)) from by
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
      by_cases hc : m * n ≤ u
      · rw [if_pos hc, if_pos hc, Nat.mul_assoc]
      · rw [if_neg hc, if_neg hc]]
    rw [dyadic_partition M (fun m => ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ u then α m * β n
            * quadEigen (grossenChar chi k) (c0 * m * n) else 0))]
    set B : ℝ := C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
        * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
        * (((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ ε)) with hB_def
    have hBnn : 0 ≤ B := by
      rw [hB_def]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) hτnn)
        (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _)
    have hLnn : (0 : ℝ) ≤ ∫ t : ℝ, |h t| := by
      apply MeasureTheory.integral_nonneg
      exact fun t => abs_nonneg (h t)
    have hterm : ∀ a ∈ Finset.range (Nat.log 2 M + 1),
        ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n
              * quadEigen (grossenChar chi k) (c0 * m * n) else 0)‖
          ≤ B * ∫ t : ℝ, |h t| := by
      intro a ha
      have hb := hypBlock_le_eps (grossenChar chi k) c0 a M N u hM hu α β hα hβ C1 ε hC1 hε
        hbound h hspec
      rw [← hB_def] at hb
      exact hb
    let g : ℕ → ℝ := fun a => ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M),
        ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then α m * β n * quadEigen (grossenChar chi k) (c0 * m * n) else 0)‖
    have hsum0 : (∑ a ∈ Finset.range (Nat.log 2 M + 1), g a)
        ≤ ((Nat.log 2 u + 1 : ℕ) : ℝ) * (B * ∫ t : ℝ, |h t|) := by
      have hzero : ∀ a ∈ Finset.range (Nat.log 2 M + 1), ¬ (1 ≤ min N (u / 2 ^ a)) →
          g a = 0 := by
        intro a ha hnot
        have hC0 : min N (u / 2 ^ a) = 0 := by
          rcases Nat.eq_zero_or_pos (min N (u / 2 ^ a)) with h1' | h1'
          · exact h1'
          · exact absurd (Nat.succ_le_of_lt h1') hnot
        dsimp only [g]
        rw [hyperbola_block_rewrite a M N u α β
          (fun m n => quadEigen (grossenChar chi k) (c0 * m * n)), hC0]
        simp
      have hsub : (∑ a ∈ Finset.range (Nat.log 2 M + 1), g a)
          = ∑ a ∈ (Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a)),
              g a :=
        (Finset.sum_subset (Finset.filter_subset _ _) (fun a ha hnotin => by
          exact hzero a ha
            (fun hcon => hnotin (Finset.mem_filter.mpr ⟨ha, hcon⟩)))).symm
      rw [hsub]
      calc ∑ a ∈ (Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a)), g a
          ≤ ∑ a ∈ (Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a)),
              (B * ∫ t : ℝ, |h t|) :=
            Finset.sum_le_sum (fun a ha => hterm a (Finset.mem_filter.mp ha).1)
        _ = (((Finset.range (Nat.log 2 M + 1)).filter
                (fun a => 1 ≤ min N (u / 2 ^ a))).card : ℝ) * (B * ∫ t : ℝ, |h t|) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((Nat.log 2 u + 1 : ℕ) : ℝ) * (B * ∫ t : ℝ, |h t|) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hBnn hLnn)
            exact_mod_cast card_dyadic_blocks M N u
    calc ‖∑ a ∈ Finset.range (Nat.log 2 M + 1),
            ∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ u then α m * β n
                * quadEigen (grossenChar chi k) (c0 * m * n) else 0)‖
        ≤ ∑ a ∈ Finset.range (Nat.log 2 M + 1), g a := norm_sum_le _ _
      _ ≤ ((Nat.log 2 u + 1 : ℕ) : ℝ) * (B * ∫ t : ℝ, |h t|) := hsum0
      _ ≤ C1 * (2 ^ ((11 : ℝ) / 12) * (2 ^ ε) * 10) * (((c0.divisors.card : ℕ) : ℝ))
            * (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) * ((u : ℝ) ^ ((11 : ℝ) / 12))
            * (((u : ℝ) + (c0 : ℝ) + 2) ^ ε)
            * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ) := by
          rw [hB_def]
          exact hypArithEps u c0 hu C1 ε (((c0.divisors.card : ℕ) : ℝ))
            (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) (∫ t : ℝ, |h t|) hC1 hε hτnn
            (Real.rpow_nonneg (by positivity) _) hLnn (le_of_lt hL1)
      _ = C1 * (2 ^ ((11 : ℝ) / 12) * (2 ^ ε) * 10) * (((c0.divisors.card : ℕ) : ℝ))
            * (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) * ((u : ℝ) ^ ((11 : ℝ) / 12))
            * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ)
            * (((u : ℝ) + (c0 : ℝ) + 2) ^ ε) := by ring

end

end Work.FIArea7.smallCInner2EpsAux
