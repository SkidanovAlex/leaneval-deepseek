/-
Row `(λ₁, λ₀) = (0.10, 2.76)` of the `λ₀` certificate `lam0_cert_rows`, for HB's
Lemma 7.2 test function at `λ = 37/20`.

The certificate is the strict failure of the `F`-inequality of HB §6 at the pair
`(λ₁, λ₀)`; by `tf72T_F_eq` the values of `F` are the closed form `G72r`, and the
whole row is the rational inequality `hnum` with the two Taylor bounds
`exp_upper12 (2·276/185)`, `exp_lower12 (2·266/185)` (`lam0_row_aux`).
-/
import Submission.Work.ZeroFreeTables.tf72G

open scoped Real BigOperators
namespace Work.ZeroFreeTables
noncomputable section

theorem lam0_row01 :
    2 * ((tf72T (37/20) (by norm_num)).F (-(276/100))
          - (tf72T (37/20) (by norm_num)).F ((1/10) - (276/100)))
      < (tf72T (37/20) (by norm_num)).F 0
        - (tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000)) := by
  have h1 : (tf72T (37/20) (by norm_num)).F (-(276/100)) = G72r (-(276/185)) := by
    rw [tf72T_F_eq (37/20) (by norm_num) (-(276/100)) (by norm_num)]
    norm_num
  have h2 : (tf72T (37/20) (by norm_num)).F ((1/10) - (276/100)) = G72r (-(266/185)) := by
    rw [tf72T_F_eq (37/20) (by norm_num) ((1/10) - (276/100)) (by norm_num)]
    norm_num
  rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
  have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
      = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
  rw [hR]
  refine lam0_row_aux (a := 276/185) (b := 266/185)
    (α := 39524904399/2000000000)
    (β := 177374048063/10000000000) ?_ ?_ ?_ ?_ ?_
  · rw [tf72B_neg_eq (by norm_num : (276/185 : ℝ) ≠ 0)]; positivity
  · rw [tf72B_neg_eq (by norm_num : (266/185 : ℝ) ≠ 0)]; positivity
  · exact exp_upper12 (2*(276/185)) (39524904399/2000000000)
      (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact exp_lower12 (2*(266/185)) (177374048063/10000000000)
      (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  · norm_num [tf72A, tf72B]

end
end Work.ZeroFreeTables
