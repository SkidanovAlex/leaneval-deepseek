/-
# ZeroFreeTables/OffAxis — `Rect2Cert`

The new numerical certificate needed by the height-`L` HB Lemma 9.4 (`OffAxis/RectLam2`):
the HB Lemma 6.2 expression with the *unconditional* constant `c = 1/6` (`ψ = 3c = 1/2`, the
supply `HB94.L52supply16`) is negative on the region `λ₁ ≤ 0.348`, `λ₂ ∈ [λ₁, 0.701]` for the
test function `tf72T (17/20)` of HB Lemma 7.2.

`Work.ZeroFreeTables.tf72_cert_of` (`table10_62_cert.lean`) is the same statement for `c = 1/8`;
`tf72_cert_of_c` here keeps `c` general, and `certA_348_701` is the instance.  By the region
reduction `tf72_region` only the corner `(λ₁, λ₂) = (0.348, 0.701)` is checked, with
`E1 = 226784/100000 ≥ e^{2·0.348/(17/20)} = 2.2678302…` (Taylor bound).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.table10_62_cert
import Submission.Work.ZeroFreeTables.tf72_exp_taylor_upper

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-! ## The `c = 1/6` certificate for the small-`λ₁` range -/

/-- **The certificate step, with a general `c`.**  `Work.ZeroFreeTables.tf72_cert_of`
(`table10_62_cert.lean`, the case `c = 1/8`) with the constant `c` of the `f(0)`-term kept
general; the proof is verbatim. -/
theorem tf72_cert_of_c {a b lam E1 c ε : ℝ} (hlam : 0 < lam) (ha : 0 < a) (hab : a ≤ b)
    (hb0 : 0 ≤ b) (hE1 : Real.exp (2*(a/lam)) ≤ E1)
    (hnum : (1/30) * ((120*E1*((a/lam)-1)^2 - 32*(a/lam)^5 + 80*(a/lam)^3
                + 120*(a/lam)^2 - 120)/(a/lam)^6 - 80/3 - Work.ZeroFreeTables.Ty6 ((a-b)/lam))
              + (16*lam/15)*(3*(c + ε)) < 0) :
    ∀ u v : ℝ, u ≤ a → u ≤ v → v ≤ b →
      (Work.ZeroFreeTables.tf72T lam hlam).F (-u) - (Work.ZeroFreeTables.tf72T lam hlam).F 0
        - (Work.ZeroFreeTables.tf72T lam hlam).F (v-u)
        + (Work.ZeroFreeTables.tf72T lam hlam).f 0 * (3*(c + ε)) < 0 := by
  intro u v hu huv hvb
  have hreg := Work.ZeroFreeTables.tf72_region lam a b u v hlam hab hb0 hu huv hvb
  have hFa := Work.ZeroFreeTables.tf72F_neg_eq lam hlam a
  have hFba := Work.ZeroFreeTables.tf72F_ba_eq lam hlam a b
  have hF0 := Work.ZeroFreeTables.tf72F_zero lam hlam
  have hx : 0 < a/lam := by positivity
  have hGup := Work.ZeroFreeTables.hb72G_le_of_exp_le hx hE1
  have hGly := Work.ZeroFreeTables.hb72G_y_lower (show (a-b)/lam ≤ 0 by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le)
  change (Work.ZeroFreeTables.tf72T lam hlam).F (-u) - (Work.ZeroFreeTables.tf72T lam hlam).F 0
      - (Work.ZeroFreeTables.tf72T lam hlam).F (v-u)
      + (Work.ZeroFreeTables.tf72f lam 0) * (3*(c + ε)) < 0
  rw [hF0, Work.ZeroFreeTables.tf72f_at_zero lam hlam]
  have h1 : (Work.ZeroFreeTables.tf72T lam hlam).F (-u)
      - (Work.ZeroFreeTables.tf72T lam hlam).F (v-u)
      ≤ Work.ZeroFreeTables.hb72G (a/lam)/30 - Work.ZeroFreeTables.Ty6 ((a-b)/lam)/30 := by
    linarith
  have h2 : Work.ZeroFreeTables.hb72G (a/lam)/30 - Work.ZeroFreeTables.Ty6 ((a-b)/lam)/30
      ≤ ((120*E1*((a/lam)-1)^2 - 32*(a/lam)^5 + 80*(a/lam)^3 + 120*(a/lam)^2 - 120)/(a/lam)^6
          - Work.ZeroFreeTables.Ty6 ((a-b)/lam))/30 := by linarith
  have hkey : (1/30)*(80/3) = 8/9 := by norm_num
  linarith [h1, h2, hnum, hkey]

/-- **The small-`λ₁` region certificate (`c = 1/6`).**  On `λ₁ ≤ 0.348`, `λ₂ ∈ [λ₁, 0.701]`
the HB Lemma 6.2 expression with `c = 1/6` and the test function `tf72T (17/20)` is negative.
By the region reduction `tf72_region` it suffices to check the corner `(0.348, 0.701)`, where
the value is `≈ -0.051`. -/
theorem certA_348_701 :
    ∀ u v : ℝ, u ≤ 348/1000 → u ≤ v → v ≤ 701/1000 →
      (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)).F (-u)
        - (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)).F 0
        - (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)).F (v-u)
        + (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)).f 0
            * (3*((1:ℝ)/6 + 1/1000000)) < 0 := by
  refine tf72_cert_of_c (a := 348/1000) (b := 701/1000) (lam := 17/20)
    (E1 := 226784/100000) (c := 1/6) (ε := 1/1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · have h2 : (2:ℝ) * (348/1000/(17/20)) = 348/425 := by norm_num
    rw [h2]
    have h := Work.ZeroFreeTables.tf72_exp_taylor_upper (348/425) (by norm_num) (by norm_num)
    refine le_trans h ?_
    norm_num [Finset.sum_range_succ]
  · rw [Work.ZeroFreeTables.Ty6_eq]
    norm_num


end Work.ZeroFreeTables.OffAxis
