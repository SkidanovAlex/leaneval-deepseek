import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.hoeffding_bounded_differences
import Submission.Work.Deep.Nibble.pi_uniform_exp_sum

namespace Work.Deep.Nibble

/-- **Hoeffding lower tail for a sum of one-coordinate functions on a product of uniform measures.**  Let `c i ≥ 1`, let `Y i · : Fin (c i) → [0, b i]` with average at least `(1-2.5κ) b i` on each coordinate, and suppose `∑ i, (b i)² ≤ 2 (∑ i, b i)² / p`.  Then on the product of the uniform measures, the probability that `j ↦ ∑ i, Y i (j i)` falls below `(1-3κ) ∑ i, b i` is at most `2 exp(-κ² p/4)`.

Indeed the expectation of the sum is `∑ i (∑ x, Y i x)/c i ≥ (1-2.5κ) ∑ i b i`, so the bad event is contained in the two-sided deviation event `{|X - E X| > κ/2 · ∑ i b i}`, to which `Work.Deep.Reed.Prob.hoeffding_bounded_differences` (with Lipschitz constants `b i`, valid because `Y i · ∈ [0, b i]`) applies, giving `2 exp(-κ² (∑ b)²/(2 ∑ b²)) ≤ 2 exp(-κ² p/4)`. -/
theorem prod_uniform_lower_tail {p : ℕ} (c : Fin p → ℕ) [∀ i, NeZero (c i)]
    {κ : ℝ} (hκ0 : 0 < κ) (b : Fin p → ℝ) (hb : ∀ i, 0 ≤ b i) (Y : ∀ i, Fin (c i) → ℝ)
    (hY0 : ∀ i j, 0 ≤ Y i j) (hYb : ∀ i j, Y i j ≤ b i)
    (hmean : ∀ i, (1 - 2.5 * κ) * b i ≤ (∑ x : Fin (c i), Y i x) / (c i : ℝ))
    (hbsq : (∑ i, (b i) ^ 2) ≤ 2 * (∑ i, b i) ^ 2 / (p : ℝ)) :
    (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).prob
        {j | (1 - 3 * κ) * (∑ i, b i) > ∑ i, Y i (j i)}
      ≤ 2 * Real.exp (-(κ ^ 2 * (p : ℝ) / 4)) := by
  classical
  -- Abbreviations: `S` the total budget, `B` the sum of squares, `m` the expectation.
  set B : ℝ := ∑ i, (b i) ^ 2 with hB
  set S : ℝ := ∑ i, b i with hS
  have hS_nonneg : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun i _ => hb i
  set m : ℝ := ∑ i, (∑ x : Fin (c i), Y i x) / (c i : ℝ) with hm
  -- The mean hypothesis, summed over the coordinates.
  have hm_ge : (1 - 2.5 * κ) * S ≤ m := by
    rw [hm, hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hmean i
  -- Fubini: the expectation of the sum is `m`.
  have hEX : (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).exp
      (fun j => ∑ i, Y i (j i)) = m := by
    rw [hm]
    exact pi_uniform_exp_sum c Y
  -- Each coordinate varies the sum by at most `b i`.
  have hlip : ∀ (i : Fin p) (f : ∀ i, Fin (c i)) (x : Fin (c i)),
      |(fun j => ∑ i, Y i (j i)) (Function.update f i x) - (fun j => ∑ i, Y i (j i)) f| ≤ b i := by
    intro i f x
    have hdiff : (∑ i' : Fin p, Y i' ((Function.update f i x) i')) - (∑ i' : Fin p, Y i' (f i'))
        = Y i x - Y i (f i) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single (s := Finset.univ)
        (f := fun i' : Fin p => Y i' ((Function.update f i x) i') - Y i' (f i')) i
        (by intro i' _ hi'; rw [Function.update_of_ne hi' x f, sub_self])
        (by intro h; exact absurd (Finset.mem_univ i) h)]
      simp
    show |(∑ i' : Fin p, Y i' ((Function.update f i x) i')) - (∑ i' : Fin p, Y i' (f i'))| ≤ b i
    rw [hdiff]
    exact abs_le.mpr ⟨by linarith [hY0 i x, hYb i (f i)], by linarith [hYb i x, hY0 i (f i)]⟩
  have ht_nonneg : 0 ≤ κ * S / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hκ0) hS_nonneg) (by norm_num)
  -- Azuma--Hoeffding with Lipschitz constants `b` and `t = κ S / 2`.
  have htail := Work.Deep.Reed.Prob.hoeffding_bounded_differences
      (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))
      (fun j => ∑ i, Y i (j i)) b hb hlip (t := κ * S / 2) ht_nonneg
  -- The bad event lies in the two-sided deviation event.
  have hsub : {j : ∀ i, Fin (c i) | (1 - 3 * κ) * S > ∑ i, Y i (j i)}
      ⊆ {f : ∀ i, Fin (c i) | κ * S / 2 < |(fun j => ∑ i, Y i (j i)) f
          - (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).exp
              (fun j => ∑ i, Y i (j i))|} := by
    intro f hf
    have hf' : (1 - 3 * κ) * S > ∑ i, Y i (f i) := by simpa only [Set.mem_ofPred_eq] using hf
    show κ * S / 2 < |(∑ i, Y i (f i))
        - (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).exp
            (fun j => ∑ i, Y i (j i))|
    rw [hEX]
    have h1 : (∑ i, Y i (f i)) - m < -(κ * S / 2) := by linarith [hm_ge, hf']
    have h2 : κ * S / 2 < -((∑ i, Y i (f i)) - m) := by linarith
    rw [abs_of_neg (by linarith)]
    exact h2
  by_cases hB0 : B = 0
  · -- Degenerate case: all the `b i` vanish, so the bad event is empty.
    have hb0 : ∀ i, b i = 0 := by
      have hsum : ∑ i, (b i) ^ 2 = 0 := by rw [← hB]; exact hB0
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i => (b i) ^ 2) (fun i _ => sq_nonneg (b i))).mp hsum
      intro i
      have hi := hall i (Finset.mem_univ i)
      nlinarith [sq_nonneg (b i), hb i]
    have hS0 : S = 0 := by rw [hS]; exact Finset.sum_eq_zero fun i _ => hb0 i
    have hbad : {j : ∀ i, Fin (c i) | (1 - 3 * κ) * S > ∑ i, Y i (j i)} = ∅ := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hS0, mul_zero]
      exact not_lt.mpr (Finset.sum_nonneg fun i _ => hY0 i (f i))
    rw [hbad, Work.Deep.Reed.FinProb.prob_empty]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · have hB_pos : 0 < B :=
      lt_of_le_of_ne (by rw [hB]; exact Finset.sum_nonneg fun i _ => sq_nonneg (b i)) (Ne.symm hB0)
    have hbsq' : B ≤ 2 * S ^ 2 / (p : ℝ) := by rw [hB, hS]; exact hbsq
    have hpos : 0 < 2 * S ^ 2 / (p : ℝ) := lt_of_lt_of_le hB_pos hbsq'
    have hp0 : p ≠ 0 := by intro hp; rw [hp] at hpos; norm_num at hpos
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp0)
    have hS_ne : S ≠ 0 := by intro h; rw [h] at hpos; norm_num at hpos
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_ne)
    have h1 : B * (p : ℝ) ≤ 2 * S ^ 2 := (le_div_iff₀ hp_pos).mp hbsq'
    -- The exponent comparison `κ² (∑ b)²/(2 ∑ b²) ≥ κ² p / 4`.
    have hkey : κ ^ 2 * (p : ℝ) / 4 ≤ 2 * (κ * S / 2) ^ 2 / B := by
      rw [le_div_iff₀ hB_pos]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg κ)]
    have hexp_le : Real.exp (-(2 * (κ * S / 2) ^ 2) / B)
        ≤ Real.exp (-(κ ^ 2 * (p : ℝ) / 4)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div]
      exact neg_le_neg hkey
    calc (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).prob
          {j | (1 - 3 * κ) * S > ∑ i, Y i (j i)}
        ≤ (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).prob
            {f | κ * S / 2 < |(fun j => ∑ i, Y i (j i)) f
              - (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).exp
                  (fun j => ∑ i, Y i (j i))|} :=
          Work.Deep.Reed.FinProb.prob_mono _ hsub
      _ ≤ 2 * Real.exp (-(2 * (κ * S / 2) ^ 2) / B) := htail
      _ ≤ 2 * Real.exp (-(κ ^ 2 * (p : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hexp_le (by norm_num)

end Work.Deep.Nibble
