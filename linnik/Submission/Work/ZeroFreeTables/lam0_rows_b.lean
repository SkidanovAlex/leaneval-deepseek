/-
Rows `(λ₁, λ₀) = (0.20,2.01), (0.25,1.77), (0.30,1.58), (0.35,1.42)` of the `λ₀`
certificate `lam0_cert_rows`, for HB's Lemma 7.2 test function at `λ = 37/20`.

Each conjunct is the strict failure of the `F`-inequality of HB §6 at the pair
`(λ₁, λ₀)`; by `tf72T_F_eq` the values of `F` are the closed form `G72r`, and the
whole row is the rational inequality `hnum` with the two Taylor bounds
(`lam0_row_aux`), exactly as in `Submission.Work.ZeroFreeTables.lam0_rows_a`.
-/
import Submission.Work.ZeroFreeTables.tf72G
import Submission.Work.ZeroFreeTables.lam0_rows_a

open scoped Real BigOperators
namespace Work.ZeroFreeTables
noncomputable section

theorem lam0_rows_b :
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(201/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((20/100) - (201/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(177/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((25/100) - (177/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(158/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((30/100) - (158/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(142/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((35/100) - (142/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- row (λ₁, λ₀) = (0.20, 2.01): a = 201/185, b = 181/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(201/100)) = G72r (-(201/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(201/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((20/100) - (201/100)) = G72r (-(181/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((20/100) - (201/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 201/185) (b := 181/185)
      (α := 87843609263/10000000000) (β := 70763395177/10000000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (201/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (181/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(201/185)) (87843609263/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(181/185)) (70763395177/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.25, 1.77): a = 177/185, b = 152/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(177/100)) = G72r (-(177/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(177/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((25/100) - (177/100)) = G72r (-(152/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((25/100) - (177/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 177/185) (b := 152/185)
      (α := 67768575989/10000000000) (β := 12929790307/2500000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (177/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (152/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(177/185)) (67768575989/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(152/185)) (12929790307/2500000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.30, 1.58): a = 158/185, b = 128/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(158/100)) = G72r (-(158/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(158/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((30/100) - (158/100)) = G72r (-(128/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((30/100) - (158/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 158/185) (b := 128/185)
      (α := 6898138961/1250000000) (β := 1994985143/500000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (158/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (128/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(158/185)) (6898138961/1250000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(128/185)) (1994985143/500000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.35, 1.42): a = 142/185, b = 107/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(142/100)) = G72r (-(142/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(142/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((35/100) - (142/100)) = G72r (-(107/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((35/100) - (142/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 142/185) (b := 107/185)
      (α := 9283905557/2000000000) (β := 7949010763/2500000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (142/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (107/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(142/185)) (9283905557/2000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(107/185)) (7949010763/2500000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]

end
end Work.ZeroFreeTables
