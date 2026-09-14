import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Algebra.BigOperators

open Finset

/-- Triangular rearrangement of a double product: summing `i ≤ m` over `m < d`. -/
lemma prod_range_prod_range_pow (r : ℕ → ℝ) (d : ℕ) :
    (∏ m ∈ Finset.range d, ∏ i ∈ Finset.range (m + 1), r i) =
      ∏ i ∈ Finset.range d, r i ^ (d - i) := by
  rw [Finset.prod_comm' (s := Finset.range d) (t := fun m => Finset.range (m + 1))
      (t' := Finset.range d) (s' := fun i => Finset.Ico i d) (f := fun _ i => r i)]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.prod_const, Nat.card_Ico]
  · intro m i
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- Telescoping product of consecutive ratios. -/
lemma prod_range_ite_div_eq (a : ℕ → ℝ) (m : ℕ) (ha : ∀ i ≤ m, a i ≠ 0) :
    (∏ i ∈ Finset.range (m + 1), (if i = 0 then a 0 else a i / a (i - 1))) = a m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => ha i (le_trans hi (Nat.le_succ m)))]
    rw [if_neg (Nat.succ_ne_zero m), Nat.succ_sub_one]
    field_simp [ha m (Nat.le_succ m)]

theorem prod_ratio_pow_telescope {d : ℕ} (a : ℕ → ℝ) (ha : ∀ j < d, a j ≠ 0) :
    (∏ j ∈ Finset.Icc 1 (d - 1), (a j / a (j - 1)) ^ (d - j)) * (a 0 / 2) ^ d =
      (∏ j ∈ Finset.range d, a j) / 2 ^ d := by
  have hP : (∏ j ∈ Finset.Icc 1 (d - 1), (a j / a (j - 1)) ^ (d - j)) * a 0 ^ d
      = ∏ j ∈ Finset.range d, a j := by
    by_cases hd : d = 0
    · subst hd; simp
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hb : ∀ m < d,
          a m = ∏ i ∈ Finset.range (m + 1), (if i = 0 then a 0 else a i / a (i - 1)) := by
        intro m hm
        exact (prod_range_ite_div_eq a m fun i hi => ha i (lt_of_le_of_lt hi hm)).symm
      have h1 : (∏ m ∈ Finset.range d, a m)
          = ∏ m ∈ Finset.range d,
              ∏ i ∈ Finset.range (m + 1), (if i = 0 then a 0 else a i / a (i - 1)) := by
        apply Finset.prod_congr rfl
        intro m hm
        exact hb m (Finset.mem_range.mp hm)
      have h2 := prod_range_prod_range_pow (fun i => if i = 0 then a 0 else a i / a (i - 1)) d
      have h3 : (∏ i ∈ Finset.range d, (if i = 0 then a 0 else a i / a (i - 1)) ^ (d - i))
          = (∏ i ∈ Finset.range (d - 1), (a (i + 1) / a i) ^ (d - 1 - i)) * a 0 ^ d := by
        have hd1 : d = (d - 1) + 1 := (Nat.succ_pred_eq_of_pos hdpos).symm
        conv_lhs => rw [hd1]
        rw [Finset.prod_range_succ']
        congr 1
        · apply Finset.prod_congr rfl
          intro i hi
          rw [if_neg (Nat.succ_ne_zero i)]
          have hsub2 : i + 1 - 1 = i := by omega
          have hsub : d - 1 + 1 - (i + 1) = d - 1 - i := by omega
          rw [hsub2, hsub]
        · rw [if_pos rfl, Nat.sub_zero, ← hd1]
      have h4 : (∏ i ∈ Finset.range (d - 1), (a (i + 1) / a i) ^ (d - 1 - i))
          = ∏ j ∈ Finset.Icc 1 (d - 1), (a j / a (j - 1)) ^ (d - j) := by
        have hIcc : Finset.Icc 1 (d - 1) = Finset.Ico 1 d := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hIcc, Finset.prod_Ico_eq_prod_range]
        apply Finset.prod_congr rfl
        intro i hi
        have e1 : 1 + i = i + 1 := by omega
        have e2 : i + 1 - 1 = i := by omega
        have e3 : d - (i + 1) = d - 1 - i := by omega
        rw [e1, e2, e3]
      rw [h1, h2, h3, h4]
  calc (∏ j ∈ Finset.Icc 1 (d - 1), (a j / a (j - 1)) ^ (d - j)) * (a 0 / 2) ^ d
      = ((∏ j ∈ Finset.Icc 1 (d - 1), (a j / a (j - 1)) ^ (d - j)) * a 0 ^ d) / 2 ^ d := by
        rw [div_pow]; ring
    _ = (∏ j ∈ Finset.range d, a j) / 2 ^ d := by rw [hP]

end Commons.Algebra.BigOperators