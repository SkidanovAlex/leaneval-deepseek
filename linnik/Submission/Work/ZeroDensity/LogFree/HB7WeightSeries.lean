import Mathlib
import Submission.Work.ZeroDensity.LogFree.HB7Defs

namespace Work.ZeroDensity.LogFree

/-- Bound for the positive half series `∑_n exp(-exp(-(n+1)η)) exp(-u n)` when `u ≥ 1`. -/
theorem HB7PosBound (η u : ℝ) (hlo : 1 ≤ u) :
    Summable (HB7P η u) ∧ (∑' n : ℕ, HB7P η u n) ≤ 2 := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-1) := le_of_lt (Real.exp_pos _)
  have hr1 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  have hle : ∀ n : ℕ, HB7P η u n ≤ 1 * (Real.exp (-1)) ^ n := by
    intro n
    rw [one_mul, HB7P_eq_exp, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hE : (0 : ℝ) ≤ Real.exp (-(((n : ℝ) + 1) * η)) := le_of_lt (Real.exp_pos _)
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hlo]
  have hf : ∀ n : ℕ, 0 ≤ HB7P η u n := fun n => by
    rw [HB7P_eq_exp]; exact le_of_lt (Real.exp_pos _)
  obtain ⟨hS, hb⟩ := summable_and_tsum_le_of_le_const_mul_pow (C := 1) zero_le_one hf hr0 hr1 hle
  refine ⟨hS, le_trans hb ?_⟩
  rw [one_mul]
  have hr2 : Real.exp (-1) ≤ 1 / 2 := exp_neg_one_le_half
  calc (1 - Real.exp (-1))⁻¹ = 1 / (1 - Real.exp (-1)) := by rw [one_div]
    _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 2 := by norm_num

/-- Bound for the negative half series `∑_n exp(-exp(n η)) exp(u (n+1))` when `1 ≤ η`, `1 ≤ u ≤ 2`. -/
theorem HB7NegBound {η u : ℝ} (hη : 1 ≤ η) (hlo : 1 ≤ u) (hhi : u ≤ 2) :
    Summable (HB7N η u) ∧ (∑' n : ℕ, HB7N η u n) ≤ 9 := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-1) := le_of_lt (Real.exp_pos _)
  have hr1 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  -- summability, via the crude majorant `exp 4 * exp(-1)^n ≥ exp(4-n)`
  have hmaj : ∀ n : ℕ, HB7N η u n ≤ Real.exp 4 * (Real.exp (-1)) ^ n := by
    intro n
    rw [HB7N_eq_exp]
    have hexp4 : Real.exp 4 * (Real.exp (-1)) ^ n = Real.exp (4 - (n : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [hexp4]
    apply Real.exp_le_exp.mpr
    rcases n with _ | _ | m
    · push_cast
      rw [zero_mul, Real.exp_zero]
      ring_nf
      linarith [hhi]
    · push_cast
      rw [one_mul]
      have hη1 : (1 : ℝ) ≤ Real.exp η := by
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp η := Real.exp_le_exp.mpr (by linarith)
      linarith [hhi, hη1]
    · push_cast
      have h3 : 3 * ((m : ℝ) + 1 + 1) ≤ Real.exp ((m : ℝ) + 1 + 1) := by
        have h := three_mul_nat_le_exp (m + 2) (by omega)
        have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 1 + 1 := by push_cast; ring
        rwa [hcast] at h
      have hmono : Real.exp ((m : ℝ) + 1 + 1) ≤ Real.exp (((m : ℝ) + 1 + 1) * η) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hη, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
      nlinarith [h3, hmono, hhi, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  have hf : ∀ n : ℕ, 0 ≤ HB7N η u n := fun n => by
    rw [HB7N_eq_exp]; exact le_of_lt (Real.exp_pos _)
  obtain ⟨hS, _⟩ :=
    summable_and_tsum_le_of_le_const_mul_pow (C := Real.exp 4)
      (le_of_lt (Real.exp_pos 4)) hf hr0 hr1 hmaj
  refine ⟨hS, ?_⟩
  have hsplit := Summable.sum_add_tsum_nat_add (f := HB7N η u) 2 hS
  rw [Finset.sum_range_succ, Finset.sum_range_one] at hsplit
  rw [← hsplit]
  have h0 : HB7N η u 0 ≤ 3 := by
    have harg : u * (((0 : ℕ) : ℝ) + 1) - Real.exp (((0 : ℕ) : ℝ) * η) = u - 1 := by
      push_cast; rw [zero_mul, Real.exp_zero]; ring
    rw [HB7N_eq_exp, harg]
    calc Real.exp (u - 1) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 := le_of_lt Real.exp_one_lt_three
  have h1 : HB7N η u 1 ≤ 4 := by
    have harg : u * (((1 : ℕ) : ℝ) + 1) - Real.exp (((1 : ℕ) : ℝ) * η) = 2 * u - Real.exp η := by
      push_cast; rw [one_mul]; ring
    rw [HB7N_eq_exp, harg]
    calc Real.exp (2 * u - Real.exp η) ≤ Real.exp (4 - Real.exp 1) := by
          apply Real.exp_le_exp.mpr
          have hη1 : Real.exp 1 ≤ Real.exp η := Real.exp_le_exp.mpr hη
          linarith
      _ ≤ 4 := le_of_lt exp_four_sub_exp_one_lt_four
  have htail : (∑' m : ℕ, HB7N η u (m + 2)) ≤ 2 := by
    have hbound : ∀ m : ℕ, HB7N η u (m + 2) ≤ (Real.exp (-1)) ^ m := by
      intro m
      rw [HB7N_eq_exp, ← Real.exp_nat_mul]
      push_cast
      apply Real.exp_le_exp.mpr
      have h3 : 3 * ((m : ℝ) + 2) ≤ Real.exp ((m : ℝ) + 2) := by
        have h := three_mul_nat_le_exp (m + 2) (by omega)
        have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
        rwa [hcast] at h
      have hmono : Real.exp ((m : ℝ) + 2) ≤ Real.exp (((m : ℝ) + 2) * η) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hη, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
      nlinarith [h3, hmono, hhi, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
    have htailS : Summable (fun m : ℕ => HB7N η u (m + 2)) :=
      Summable.of_nonneg_of_le (fun m => by rw [HB7N_eq_exp]; exact le_of_lt (Real.exp_pos _))
        hbound (summable_geometric_of_lt_one hr0 hr1)
    refine le_trans (htailS.tsum_le_tsum hbound (summable_geometric_of_lt_one hr0 hr1)) ?_
    exact tsum_pow_le_two hr0 exp_neg_one_le_half
  linarith

theorem HB7WeightSeries {η a : ℝ} (hη : 1 ≤ η) (hlo : 1 ≤ 2 * a * η) (hhi : 2 * a * η ≤ 2) :
    (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * η))))
      * Real.exp (-(2 * a * (j : ℝ) * η))) ≤ 12 := by
  set F : ℤ → ℝ := fun j => Real.exp (-(Real.exp (-(((j : ℝ) + 1) * η))))
      * Real.exp (-(2 * a * (j : ℝ) * η)) with hFdef
  have hP : (fun n : ℕ => F (n : ℤ)) = HB7P η (2 * a * η) := by
    funext n
    simp only [hFdef, HB7P, Int.cast_natCast]
    rw [show -(2 * a * (n : ℝ) * η) = -((2 * a * η) * (n : ℝ)) by ring]
  have hN : (fun n : ℕ => F (-((n : ℤ) + 1))) = HB7N η (2 * a * η) := by
    funext n
    simp only [hFdef, HB7N]
    push_cast
    rw [show -((-((n : ℝ) + 1) + 1) * η) = (n : ℝ) * η by ring]
    rw [show -(2 * a * (-((n : ℝ) + 1)) * η) = (2 * a * η) * ((n : ℝ) + 1) by ring]
  have hPS : Summable (fun n : ℕ => F (n : ℤ)) := by
    rw [hP]; exact (HB7PosBound η (2 * a * η) hlo).1
  have hNS : Summable (fun n : ℕ => F (-((n : ℤ) + 1))) := by
    rw [hN]; exact (HB7NegBound hη hlo hhi).1
  have hsplit := tsum_of_nat_of_neg_add_one hPS hNS
  rw [hP, hN] at hsplit
  rw [hsplit]
  have hPb := (HB7PosBound η (2 * a * η) hlo).2
  have hNb := (HB7NegBound hη hlo hhi).2
  linarith

end Work.ZeroDensity.LogFree
