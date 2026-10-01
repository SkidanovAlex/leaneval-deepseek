import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs
import Submission.Work.LinnikAreas.Density4.sqfree_pf_sum_le_powerset
import Submission.Work.LinnikAreas.Density4.sum_prime_sqrt_weight_le
import Submission.Work.LinnikAreas.Density4.cw_two_pow_mul_sqrt

namespace Work.LinnikAreas.Density4

open Finset BigOperators

noncomputable section

private lemma log_le_two_sqrt (u : ℕ) : Real.log (u : ℝ) ≤ 2 * Real.sqrt (u : ℝ) := by
  rcases Nat.eq_zero_or_pos u with h | h
  · subst h; simp
  · have h1 : Real.log (u : ℝ) ≤ (u : ℝ) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 : Real.sqrt (u : ℝ) / ((1 : ℝ) / 2) = 2 * Real.sqrt (u : ℝ) := by ring
    linarith

private lemma one_add_log_le_three_sqrt (u : ℕ) (hu : 1 ≤ u) :
    1 + Real.log (u : ℝ) ≤ 3 * Real.sqrt (u : ℝ) := by
  have h1 : Real.log (u : ℝ) ≤ 2 * Real.sqrt (u : ℝ) := log_le_two_sqrt u
  have h2 : (1 : ℝ) ≤ Real.sqrt (u : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hu)
  linarith

lemma sum_sqfree_cw_sqrt_le (M : ℕ) :
    (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
        cw u * (2 : ℝ) ^ (u.primeFactors.card) * Real.sqrt (u : ℝ)) ≤ Real.exp 16 := by
  set P : Finset ℕ := (Finset.Icc 2 M).filter Nat.Prime with hP
  set b : ℕ → ℝ := fun p => 2 / ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt (p : ℝ) with hb
  have hb0 : ∀ p, 0 ≤ b p := by
    intro p
    rw [hb]
    rcases Nat.lt_or_ge p 2 with h | h
    · have hp : p = 0 ∨ p = 1 := by omega
      rcases hp with rfl | rfl <;> norm_num
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
      have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      exact mul_nonneg (div_nonneg (by norm_num) (le_of_lt hden)) (Real.sqrt_nonneg _)
  calc (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
          cw u * (2 : ℝ) ^ (u.primeFactors.card) * Real.sqrt (u : ℝ))
      = ∑ u ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ u.primeFactors, b p := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hb]
        exact cw_two_pow_mul_sqrt u (Finset.mem_filter.mp hu).2
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, b p := sqfree_pf_sum_le_powerset M b hb0
    _ = ∏ p ∈ P, (1 + b p) := (Finset.prod_one_add P (f := b)).symm
    _ ≤ Real.exp (∑ p ∈ P, b p) := Real.prod_one_add_le_exp_sum P hb0
    _ ≤ Real.exp 16 := by
        apply Real.exp_le_exp.mpr
        rw [hP, hb]
        exact sum_prime_sqrt_weight_le M

theorem sum_sqfree_cw_two_pow_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ M : ℕ, (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
        cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u)) ≤ C) ∧
    (∀ N M : ℕ, 1 ≤ N → (∑ u ∈ (Finset.Icc (N+1) M).filter Squarefree,
        cw u * (2:ℝ)^(u.primeFactors.card)) ≤ C * (1 + Real.log N) / Real.sqrt N) := by
  refine ⟨3 * Real.exp 16, by positivity, ?_, ?_⟩
  · intro M
    calc (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
            cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log (u:ℝ)))
        ≤ ∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
            cw u * (2:ℝ)^(u.primeFactors.card) * (3 * Real.sqrt (u:ℝ)) := by
          refine Finset.sum_le_sum fun u hu => ?_
          have h1 : 1 ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1
          have hlog : 1 + Real.log (u:ℝ) ≤ 3 * Real.sqrt (u:ℝ) := one_add_log_le_three_sqrt u h1
          have hnn : 0 ≤ cw u * (2:ℝ)^(u.primeFactors.card) :=
            mul_nonneg (cw_nonneg u) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog hnn
      _ = 3 * (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
            cw u * (2:ℝ)^(u.primeFactors.card) * Real.sqrt (u:ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          ring
      _ ≤ 3 * Real.exp 16 := by
          have := sum_sqfree_cw_sqrt_le M
          linarith
  · intro N M hN
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hsqrtN : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNpos
    have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    set s2 : Finset ℕ := (Finset.Icc (N+1) M).filter Squarefree with hs2
    have hkey : (∑ u ∈ s2, cw u * (2:ℝ)^(u.primeFactors.card)) ≤ Real.exp 16 / Real.sqrt (N:ℝ) := by
      have hA : ∀ u ∈ s2, cw u * (2:ℝ)^(u.primeFactors.card)
            ≤ cw u * (2:ℝ)^(u.primeFactors.card) * Real.sqrt (u:ℝ) / Real.sqrt (N:ℝ) := by
        intro u hu
        rw [hs2, Finset.mem_filter, Finset.mem_Icc] at hu
        have hNu : (N:ℝ) ≤ (u:ℝ) := by
          have h1 : N ≤ u := Nat.le_trans (Nat.le_succ N) hu.1.1
          exact_mod_cast h1
        have hs : Real.sqrt (N:ℝ) ≤ Real.sqrt (u:ℝ) := Real.sqrt_le_sqrt hNu
        have hnn : 0 ≤ cw u * (2:ℝ)^(u.primeFactors.card) :=
          mul_nonneg (cw_nonneg u) (by positivity)
        rw [le_div_iff₀ hsqrtN]
        exact mul_le_mul_of_nonneg_left hs hnn
      calc (∑ u ∈ s2, cw u * (2:ℝ)^(u.primeFactors.card))
          ≤ ∑ u ∈ s2, cw u * (2:ℝ)^(u.primeFactors.card) * Real.sqrt (u:ℝ) / Real.sqrt (N:ℝ) :=
            Finset.sum_le_sum hA
        _ = (∑ u ∈ s2, cw u * (2:ℝ)^(u.primeFactors.card) * Real.sqrt (u:ℝ)) / Real.sqrt (N:ℝ) := by
            rw [Finset.sum_div]
        _ ≤ (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
                cw u * (2:ℝ)^(u.primeFactors.card) * Real.sqrt (u:ℝ)) / Real.sqrt (N:ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hsqrtN)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [hs2, Finset.mem_filter, Finset.mem_Icc] at hx
              rw [Finset.mem_filter, Finset.mem_Icc]
              exact ⟨⟨by omega, hx.1.2⟩, hx.2⟩
            · intro x hx1 hx2
              exact mul_nonneg (mul_nonneg (cw_nonneg x) (by positivity)) (Real.sqrt_nonneg _)
        _ ≤ Real.exp 16 / Real.sqrt (N:ℝ) :=
            div_le_div_of_nonneg_right (sum_sqfree_cw_sqrt_le M) (le_of_lt hsqrtN)
    calc (∑ u ∈ (Finset.Icc (N+1) M).filter Squarefree, cw u * (2:ℝ)^(u.primeFactors.card))
        = ∑ u ∈ s2, cw u * (2:ℝ)^(u.primeFactors.card) := by rw [hs2]
      _ ≤ Real.exp 16 / Real.sqrt (N:ℝ) := hkey
      _ ≤ (3 * Real.exp 16) * (1 + Real.log (N:ℝ)) / Real.sqrt (N:ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hsqrtN)
          have hexp : (0:ℝ) < Real.exp 16 := Real.exp_pos 16
          nlinarith [hexp]

end

end Work.LinnikAreas.Density4

