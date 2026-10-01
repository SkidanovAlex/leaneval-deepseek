/-
Rows `(λ₁, λ₀) = (0.12,2.56), (0.14,2.39), (0.16,2.25), (0.18,2.12)` of the `λ₀`
certificate `lam0_cert_rows`, for HB's Lemma 7.2 test function at `λ = 37/20`.

Each conjunct is the strict failure of the `F`-inequality of HB §6 at the pair
`(λ₁, λ₀)`; by `tf72T_F_eq` the values of `F` are the closed form `G72r`, and the
whole row is the rational inequality `hnum` with the two Taylor bounds
(`lam0_row_aux`), exactly as in `Submission.Work.ZeroFreeTables.lam0_row01`.
-/
import Submission.Work.ZeroFreeTables.tf72G
import Submission.Work.ZeroFreeTables.lam0_row01

open scoped Real BigOperators
namespace Work.ZeroFreeTables
noncomputable section

theorem lam0_rows_a :
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(256/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((12/100) - (256/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(239/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((14/100) - (239/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(225/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((16/100) - (225/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) ∧
    (2 * ((Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F (-(212/100))
            - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F ((18/100) - (212/100)))
        < (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).F 0
          - (Work.ZeroFreeTables.tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- row (λ₁, λ₀) = (0.12, 2.56): a = 256/185, b = 244/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(256/100)) = G72r (-(256/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(256/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((12/100) - (256/100)) = G72r (-(244/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((12/100) - (256/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 256/185) (b := 244/185)
      (α := 159198628841/10000000000) (β := 139829375209/10000000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (256/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (244/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(256/185)) (159198628841/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(244/185)) (139829375209/10000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.14, 2.39): a = 239/185, b = 45/37
    have h1 : (tf72T (37/20) (by norm_num)).F (-(239/100)) = G72r (-(239/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(239/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((14/100) - (239/100)) = G72r (-(45/37)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((14/100) - (239/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 239/185) (b := 45/37)
      (α := 66235839341/5000000000) (β := 711659089/62500000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (239/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (45/37 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(239/185)) (66235839341/5000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(45/37)) (711659089/62500000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.16, 2.25): a = 45/37, b = 209/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(225/100)) = G72r (-(45/37)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(225/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((16/100) - (225/100)) = G72r (-(209/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((16/100) - (225/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 45/37) (b := 209/185)
      (α := 56932727121/5000000000) (β := 47889552591/5000000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (45/37 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (209/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(45/37)) (56932727121/5000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(209/185)) (47889552591/5000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]
  · -- row (λ₁, λ₀) = (0.18, 2.12): a = 212/185, b = 194/185
    have h1 : (tf72T (37/20) (by norm_num)).F (-(212/100)) = G72r (-(212/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) (-(212/100)) (by norm_num)]
      norm_num
    have h2 : (tf72T (37/20) (by norm_num)).F ((18/100) - (212/100)) = G72r (-(194/185)) := by
      rw [tf72T_F_eq (37/20) (by norm_num) ((18/100) - (212/100)) (by norm_num)]
      norm_num
    rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
    have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
        = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
    rw [hR]
    refine lam0_row_aux (a := 212/185) (b := 194/185)
      (α := 49468188397/5000000000) (β := 40720644907/5000000000) ?_ ?_ ?_ ?_ ?_
    · rw [tf72B_neg_eq (by norm_num : (212/185 : ℝ) ≠ 0)]; positivity
    · rw [tf72B_neg_eq (by norm_num : (194/185 : ℝ) ≠ 0)]; positivity
    · exact exp_upper12 (2*(212/185)) (49468188397/5000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
    · exact exp_lower12 (2*(194/185)) (40720644907/5000000000)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
        (by norm_num [Finset.sum_range_succ])
    · norm_num [tf72A, tf72B]

end
end Work.ZeroFreeTables
