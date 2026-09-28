import Mathlib
import Submission.Work.HP.MM2.f_zero_le
import Submission.Work.HP.MM2.f_one_le
import Submission.Work.HP.MM2.f_high_le

namespace Work.HP.MM2

/-- Bound for the double dyadic sum
`∑_{j ≤ J} (2^{j+1}/T) · ∑_{m ≤ R} (T/2^j)^m A_m`.

The inner double sum splits according to `m`.  Swapping the two sums, each `m`-slice is the
one-dimensional sum `f m = ∑_{j ≤ J} (2^{j+1}/T)·(T/2^j)^m·A_m`, which is controlled by
`f_zero_le`, `f_one_le` and `f_high_le` for `m = 0`, `m = 1` and `m ≥ 2` respectively. -/
theorem dyadic_double_sum (R J : ℕ) (T : ℝ) (A : ℕ → ℝ) (hT : 1 ≤ T) (hJ : (2:ℝ)^J ≤ T)
    (hA : ∀ m, 0 ≤ A m) :
    (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * (∑ m ∈ Finset.range (R+1), (T/(2:ℝ)^j)^m * A m))
      ≤ 4*A 0 + 4*((J:ℝ)+1)*A 1 + 4*∑ m ∈ Finset.range (R+1), T^(m-1) * A m := by
  have hTpos : (0:ℝ) < T := by linarith
  let f : ℕ → ℝ := fun m => ∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^m * A m)
  have hf_nonneg : ∀ m, 0 ≤ f m := by
    intro m
    apply Finset.sum_nonneg
    intro j _
    have h1 : (0:ℝ) ≤ (2:ℝ)^(j+1)/T := div_nonneg (by positivity) (le_of_lt hTpos)
    have h2 : (0:ℝ) ≤ (T/(2:ℝ)^j)^m := pow_nonneg (div_nonneg (le_of_lt hTpos) (by positivity)) m
    exact mul_nonneg h1 (mul_nonneg h2 (hA m))
  have hf0 : f 0 ≤ 4 * A 0 := by
    dsimp only [f]
    exact f_zero_le J T A hT hJ (hA 0)
  have hf1 : f 1 ≤ 4 * ((J:ℝ)+1) * A 1 := by
    dsimp only [f]
    exact f_one_le J T A hT (hA 1)
  have hfm : ∀ m, 2 ≤ m → f m ≤ 4 * T^(m-1) * A m := by
    intro m hm
    dsimp only [f]
    exact f_high_le J m T A hT hm (hA m)
  have hLHS : (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * (∑ m ∈ Finset.range (R+1), (T/(2:ℝ)^j)^m * A m))
      = ∑ m ∈ Finset.range (R+1), f m := by
    rw [show (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * (∑ m ∈ Finset.range (R+1), (T/(2:ℝ)^j)^m * A m))
        = ∑ j ∈ Finset.range (J+1), ∑ m ∈ Finset.range (R+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^m * A m) from by
          apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]]
    exact Finset.sum_comm
  rw [hLHS]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (R+1)) (fun m => m ≤ 1) f]
  have hlow : (∑ m ∈ (Finset.range (R+1)).filter (fun m => m ≤ 1), f m)
      ≤ 4*A 0 + 4*((J:ℝ)+1)*A 1 := by
    have hsub : (Finset.range (R+1)).filter (fun m => m ≤ 1) ⊆ Finset.range 2 := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      omega
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hf_nonneg m)
    have h2 : (∑ m ∈ Finset.range 2, f m) = f 0 + f 1 := by simp [Finset.sum_range_succ]
    linarith [h, h2, hf0, hf1]
  have hhigh : (∑ m ∈ (Finset.range (R+1)).filter (fun m => ¬ m ≤ 1), f m)
      ≤ 4 * ∑ m ∈ Finset.range (R+1), T^(m-1) * A m := by
    have hpt : ∀ m ∈ (Finset.range (R+1)).filter (fun m => ¬ m ≤ 1),
        f m ≤ 4 * (T^(m-1) * A m) := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      have hm2 : 2 ≤ m := by omega
      calc f m ≤ 4 * T^(m-1) * A m := hfm m hm2
        _ = 4 * (T^(m-1) * A m) := by ring
    calc (∑ m ∈ (Finset.range (R+1)).filter (fun m => ¬ m ≤ 1), f m)
        ≤ ∑ m ∈ (Finset.range (R+1)).filter (fun m => ¬ m ≤ 1), 4 * (T^(m-1) * A m) :=
          Finset.sum_le_sum hpt
      _ = 4 * ∑ m ∈ (Finset.range (R+1)).filter (fun m => ¬ m ≤ 1), T^(m-1) * A m := by
          rw [Finset.mul_sum]
      _ ≤ 4 * ∑ m ∈ Finset.range (R+1), T^(m-1) * A m := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset (fun m => ¬ m ≤ 1) (Finset.range (R+1)))
          intro m hm _
          exact mul_nonneg (pow_nonneg (le_of_lt hTpos) _) (hA m)
  linarith [hlow, hhigh]

end Work.HP.MM2
