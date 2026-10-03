import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.MeanInequalities

theorem sum_rpow_holder {F R : ℕ → ℝ} (hF : ∀ d, 0 ≤ F d) (hR : ∀ d, 0 ≤ R d) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, F d ^ 5 * R d)
      ≤ (∑ d ∈ Finset.Icc 1 D, F d ^ (20 / 3 : ℝ) * R d) ^ (3 / 4 : ℝ)
        * (∑ d ∈ Finset.Icc 1 D, R d) ^ (1 / 4 : ℝ) := by
  have hconj : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hF5 : ∀ d, 0 ≤ F d ^ (5 : ℝ) := fun d => Real.rpow_nonneg (hF d) 5
  have hR34 : ∀ d, 0 ≤ R d ^ (3 / 4 : ℝ) := fun d => Real.rpow_nonneg (hR d) (3 / 4)
  have hR14 : ∀ d, 0 ≤ R d ^ (1 / 4 : ℝ) := fun d => Real.rpow_nonneg (hR d) (1 / 4)
  -- pointwise identities
  have hid1 : ∀ d, F d ^ 5 * R d
      = (F d ^ (5 : ℝ) * R d ^ (3 / 4 : ℝ)) * R d ^ (1 / 4 : ℝ) := by
    intro d
    rw [mul_assoc, ← Real.rpow_add_of_nonneg (hR d) (by norm_num) (by norm_num)]
    rw [show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
    norm_num
  have hid2 : ∀ d, (F d ^ (5 : ℝ) * R d ^ (3 / 4 : ℝ)) ^ (4 / 3 : ℝ)
      = F d ^ (20 / 3 : ℝ) * R d := by
    intro d
    rw [Real.mul_rpow (hF5 d) (hR34 d), ← Real.rpow_mul (hF d), ← Real.rpow_mul (hR d)]
    rw [show (5 : ℝ) * (4 / 3) = 20 / 3 by norm_num,
      show (3 : ℝ) / 4 * (4 / 3) = 1 by norm_num, Real.rpow_one]
  have hid3 : ∀ d, (R d ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = R d := by
    intro d
    rw [← Real.rpow_mul (hR d)]
    rw [show (1 : ℝ) / 4 * 4 = 1 by norm_num, Real.rpow_one]
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.Icc 1 D)
      (f := fun d => F d ^ (5 : ℝ) * R d ^ (3 / 4 : ℝ))
      (g := fun d => R d ^ (1 / 4 : ℝ))
      (p := (4 / 3 : ℝ)) (q := 4) hconj
      (fun i _ => mul_nonneg (hF5 i) (hR34 i)) (fun i _ => hR14 i)
  calc (∑ d ∈ Finset.Icc 1 D, F d ^ 5 * R d)
      = ∑ d ∈ Finset.Icc 1 D,
          (F d ^ (5 : ℝ) * R d ^ (3 / 4 : ℝ)) * R d ^ (1 / 4 : ℝ) :=
        Finset.sum_congr rfl (fun d _ => hid1 d)
    _ ≤ (∑ d ∈ Finset.Icc 1 D, (F d ^ (5 : ℝ) * R d ^ (3 / 4 : ℝ)) ^ (4 / 3 : ℝ))
            ^ (1 / (4 / 3 : ℝ))
          * (∑ d ∈ Finset.Icc 1 D, (R d ^ (1 / 4 : ℝ)) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := key
    _ = (∑ d ∈ Finset.Icc 1 D, F d ^ (20 / 3 : ℝ) * R d) ^ (3 / 4 : ℝ)
          * (∑ d ∈ Finset.Icc 1 D, R d) ^ (1 / 4 : ℝ) := by
        rw [Finset.sum_congr rfl (fun d _ => hid2 d), Finset.sum_congr rfl (fun d _ => hid3 d),
          show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num]

end Commons.Analysis.MeanInequalities