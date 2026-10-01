/-
Rows `(λ₁, λ₀) = (0.40,2.29), (0.45,2.18), (0.50,2.08)` of the `λ₀`
certificate `lam0_cert_rows`, for HB's Lemma 7.2 test function at `λ = 37/20`.

Each conjunct is the strict failure of the `F`-inequality of HB §6 at the pair
`(λ₁, λ₀)`; by `tf72T_F_eq` the values of `F` are the closed form `G72r`, and the
whole row is the rational inequality `hnum` with the two Taylor bounds
(`lam0_row_aux`), exactly as in `Submission.Work.ZeroFreeTables.lam0_rows_a`.
-/
import Submission.Work.ZeroFreeTables.tf72G
import Submission.Work.ZeroFreeTables.lam0_row01

open scoped Real BigOperators
namespace Work.ZeroFreeTables
noncomputable section

theorem lam0_rows_c :
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(129/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((40/100) - (129/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(118/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((45/100) - (118/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(108/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((50/100) - (108/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- row (λ₁, λ₀) = (0.40, 2.29): a = 129/185, b = 89/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(129/100)) = G72r (-(129/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(129/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((40/100) - (129/100)) = G72r (-(89/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((40/100) - (129/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 129/185) (b := 89/185)
      (α := 40333391037/10000000000) (β := 26173494937/10000000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (129/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (89/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(129/185)) (40333391037/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(89/185)) (26173494937/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.45, 2.18): a = 118/185, b = 73/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(118/100)) = G72r (-(118/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(118/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((45/100) - (118/100)) = G72r (-(73/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((45/100) - (118/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 118/185) (b := 73/185)
      (α := 35811202687/10000000000) (β := 176128849/80000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (118/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (73/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(118/185)) (35811202687/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(73/185)) (176128849/80000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.50, 2.08): a = 108/185, b = 58/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(108/100)) = G72r (-(108/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(108/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((50/100) - (108/100)) = G72r (-(58/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((50/100) - (108/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 108/185) (b := 58/185)
      (α := 32141648833/10000000000) (β := 18720367831/10000000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (108/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (58/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(108/185)) (32141648833/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(58/185)) (18720367831/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]

end
end Work.ZeroFreeTables
