import Mathlib
import Submission.Work.ZeroFreeTables.table10_62_cert
import Submission.Work.ZeroFreeTables.tf72_exp_taylor_upper
import Submission.Work.ZeroFreeTables.T10Defs
import Submission.Work.ZeroFreeTables.testFn7_2

namespace Work.ZeroFreeTables.HB94

open Work.ZeroFreeTables

/-!
# The region certificate of HB Lemma 6.2 for the real case of Lemma 9.4

`λ₁ < 0.348` forces `χ₁` real and `ρ₁` real (HB Theorem 1), whereupon the five-term inequality of
HB Lemma 6.2 is available with the per-character constants `c₁ = φ(χ₁)/2 = 1/8` (from
`L52Hyp_eighth_le4`, `χ₁² = 1`) and `c₂ = c₃ = c₄ = 1/6` (from the unconditional supply), i.e.
`ψ = 1/8 + 1/6 + 1/6 = 11/24`.  The region is `u = λ₁ ∈ [0, 348/1000]`, `v = λ₂ ∈ [u, 929/1000]`
(`929/1000` is the largest entry of Table 10).

This file is `Work.ZeroFreeTables.table10_62_cert` with `ψ = 3/8` replaced by `ψ = 11/24`: the
certificate step `tf72_cert_of` is copied verbatim (as `tf72_cert_of_real`) with the new constant,
and the single corner `(a,b) = (348/1000, 929/1000)` with `λ = 22/25` is certified numerically.  The
worst point of the region is the corner `(a,b)`, where the left-hand side is `≈ -0.0081`
(`F(-a/λ) = tf72Phi(-87/220) ≈ 1.10137`, `F(0) = 8/9`, `F(0.581/λ) = tf72Phi(581/880) ≈ 0.65082`),
and at `(0, 929/1000)` it is `≈ -0.1229`; the region reduction `tf72_region` (monotonicity of
`F(-u) - F(v-u)` in `u` and in `v`) bounds every other point of the region by the corner. -/

/-- **The certificate step with `ψ = 11/24`** (copy of `Work.ZeroFreeTables.tf72_cert_of` with the
constant `3*(1/8 + 1/1000000)` replaced by `11/24 + 1/1000000`). -/
theorem tf72_cert_of_real {a b lam E1 : ℝ} (hlam : 0 < lam) (ha : 0 < a) (hab : a ≤ b)
    (hb0 : 0 ≤ b) (hE1 : Real.exp (2*(a/lam)) ≤ E1)
    (hnum : (1/30) * ((120*E1*((a/lam)-1)^2 - 32*(a/lam)^5 + 80*(a/lam)^3
                + 120*(a/lam)^2 - 120)/(a/lam)^6 - 80/3 - Ty6 ((a-b)/lam))
              + (16*lam/15)*((11:ℝ)/24 + 1/1000000) < 0) :
    ∀ u v : ℝ, u ≤ a → u ≤ v → v ≤ b →
      (tf72T lam hlam).F (-u) - (tf72T lam hlam).F 0 - (tf72T lam hlam).F (v-u)
        + (tf72T lam hlam).f 0 * ((11:ℝ)/24 + 1/1000000) < 0 := by
  intro u v hu huv hvb
  have hreg := tf72_region lam a b u v hlam hab hb0 hu huv hvb
  have hFa := tf72F_neg_eq lam hlam a
  have hFba := tf72F_ba_eq lam hlam a b
  have hF0 := tf72F_zero lam hlam
  have hx : 0 < a/lam := by positivity
  have hGup := hb72G_le_of_exp_le hx hE1
  have hGly := hb72G_y_lower (show (a-b)/lam ≤ 0 by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le)
  change (tf72T lam hlam).F (-u) - (tf72T lam hlam).F 0 - (tf72T lam hlam).F (v-u)
      + (tf72f lam 0) * ((11:ℝ)/24 + 1/1000000) < 0
  rw [hF0, tf72f_at_zero lam hlam]
  have h1 : (tf72T lam hlam).F (-u) - (tf72T lam hlam).F (v-u)
      ≤ hb72G (a/lam)/30 - Ty6 ((a-b)/lam)/30 := by linarith
  have h2 : hb72G (a/lam)/30 - Ty6 ((a-b)/lam)/30
      ≤ ((120*E1*((a/lam)-1)^2 - 32*(a/lam)^5 + 80*(a/lam)^3 + 120*(a/lam)^2 - 120)/(a/lam)^6
          - Ty6 ((a-b)/lam))/30 := by linarith
  have hkey : (1/30)*(80/3) = 8/9 := by norm_num
  linarith [h1, h2, hnum, hkey]

/-- **The region certificate of HB Lemma 6.2 with `ψ = 11/24`** on the real-case region
`λ₁ ∈ [0, 348/1000]`, `λ₂ ∈ [λ₁, 929/1000]`. -/
theorem table10_62_cert_real :
    ∃ (lam : ℝ) (hl : 0 < lam),
      ∀ u v : ℝ, 0 ≤ u → u ≤ 348/1000 → u ≤ v → v ≤ 929/1000 →
        (tf72T lam hl).F (-u) - (tf72T lam hl).F 0 - (tf72T lam hl).F (v - u)
          + (tf72T lam hl).f 0 * ((11:ℝ)/24 + 1/1000000) < 0 := by
  have hl : (0:ℝ) < ((22:ℝ)/25) := by norm_num
  refine ⟨((22:ℝ)/25), hl, fun u v _hu0 hua huv hvb => ?_⟩
  refine tf72_cert_of_real (a := ((348:ℝ)/1000)) (b := ((929:ℝ)/1000)) (lam := ((22:ℝ)/25))
    (E1 := ((2205401:ℝ)/1000000)) hl (by norm_num) (by norm_num) (by norm_num) ?_ ?_ u v hua huv hvb
  · have hq : 2 * (((348:ℝ)/1000) / ((22:ℝ)/25)) = ((87:ℝ)/110) := by norm_num
    rw [hq]
    refine le_trans (tf72_exp_taylor_upper (((87:ℝ)/110)) (by norm_num) (by norm_num)) ?_
    norm_num [Finset.sum_range_succ]
  · norm_num [Ty6_eq]

end Work.ZeroFreeTables.HB94
