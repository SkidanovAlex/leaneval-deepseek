import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixKin.FSRegime
import Submission.Work.BoseKinLoc.Assembly.tprR_branches_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixKin.Assembly

open Work.BoseFixKin

/-!
# `Work.BoseFixKin.Assembly.region_far_far` — Region III of the coupled scalar budget

The third and last of the three regional cases of `core_budget_fs` (node N1 of
`BOSE_BCLASH_LEAD.md` §3): both two-regime kernels are on their **far** branch, i.e.
`q ≥ (5/6)(2s)⁻¹` **and** `q ≥ (5/6)(2ds)⁻¹`.  Since `d ≤ 1` the second condition is the
stronger one, so this is the region `q ≥ 5/(12ds)`.

## Contents

* `cFS_le_quarter` — `cFS K C ≤ 1/4`;
* `half_one_add_mul_cFS_le` — `(1+K)/2 · cFS K C ≤ 1/128`, the absorption of the
  momentum factor `K` by the regime constant;
* `region_far_far` — the regional budget.

## Proof

`tprR (2s) C q = (q - (4s)⁻¹)²` and `tprR (2ds) C q = (q - (4ds)⁻¹)²` (`tprR_far_gen`).
Split the four terms into the *Bogolubov pair* `T1 + T2` and the *cut-off pair* `T3 + T4`:

* **Bogolubov pair.**  `T1 = A εT q²/(1+d²q²) ≤ A εT q/(2d)` by AM–GM
  (`1 + (dq)² ≥ 2dq`), `= (Aq/2)(εT/d) ≤ (Aq/2)(c/s) ≤ (1/256)(q/s)` using the coupling
  `εT s ≤ c d` and `A c ≤ 1/128`; and `T2 = 2b q²/(q²+1/2) ≤ 2b ≤ 1/8`.  Since
  `q ≥ 5/(12ds)` with `d ≤ 1`, `s ≤ 1/4` gives `q/s ≥ 20/3`, and
  `(7/20 - 1/256)(20/3) > 1/8`, so `T1 + T2 ≤ (7/20)(q/s)`.
* **Cut-off pair.**  With `a := (4s)⁻¹`, `q² - (q-a)² = 2qa - a² ≥ (7/5)qa = (7/20)(q/s)`
  because `a ≤ (3/5)q`; likewise for `a' := (4ds)⁻¹`.  Hence
  `T3 + T4 ≤ q² - (1-εT)(7/20)(q/s) - εT(7/20)(q/(ds))`.
* Finally `q/(ds) ≥ q/s` (`d ≤ 1`), so `(7/20)(q/s) ≤ (1-εT)(7/20)(q/s) + εT(7/20)(q/(ds))`
  and adding the two displays gives `T1 + T2 + T3 + T4 ≤ q²`.
-/

/-- The regime constant is at most `1/4`. -/
lemma cFS_le_quarter (K C : ℝ) : cFS K C ≤ 1 / 4 := min_le_left _ _

/-- **The momentum factor `K` is absorbed by the regime constant**: `(1+K)/2 · cFS K C ≤ 1/128`.
Indeed `cFS K C ≤ 1/(64(K+C+1))` and `(1+K)/(K+C+1) ≤ 1` because `C > 0`. -/
lemma half_one_add_mul_cFS_le (K C : ℝ) (hK : 0 ≤ K) (hC : 0 < C) :
    (1 + K) / 2 * cFS K C ≤ 1 / 128 := by
  have h1 : cFS K C ≤ 1 / (64 * (K + C + 1)) := min_le_right _ _
  have h2 : (1 + K) / 2 * (1 / (64 * (K + C + 1))) = (K + 1) / (128 * (K + C + 1)) := by
    field_simp
    ring
  have h3 : (K + 1) / (128 * (K + C + 1)) ≤ 1 / 128 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 128)]
    nlinarith [hK, hC.le]
  calc (1 + K) / 2 * cFS K C ≤ (1 + K) / 2 * (1 / (64 * (K + C + 1))) := by
        apply mul_le_mul_of_nonneg_left h1; linarith
    _ = (K + 1) / (128 * (K + C + 1)) := h2
    _ ≤ 1 / 128 := h3

set_option maxHeartbeats 1000000 in
/-- **Region III (both branches far) of the three-region budget for `core_budget_fs`.**
`tprR (2s) C q = (q - (4s)⁻¹)²` and `tprR (2ds) C q = (q - (4ds)⁻¹)²` (`tprR_far_gen`).
With `a := (4s)⁻¹`, `a' := (4ds)⁻¹`, `q ≥ (5/6)(2ds)⁻¹ ≥ (5/6)(2s)⁻¹` gives
`q ≥ (5/3)a` and `q ≥ (5/3)a'`, whence
`q² - T3 - T4 ≥ (1-εT)(7/20)(q/s) + εT(7/20)(q/(ds))`.
It remains to pay `T1 + T2`:
* `T1 ≤ A εT q/(2d) ≤ (A c/2)(q/s)` by AM–GM and the coupling `εT s ≤ c d` (`s > 0`),
  `A := (1+K)/2`, `c := cFS K C`, `A c ≤ 1/128`;
* `T2 = 2b q²/(q²+1/2) ≤ 2b ≤ 1/8`;
* `q/s ≥ 5/(12d s²) ≥ 20/3` (from `q ≥ 5/(12ds)`, `d ≤ 1`, `s ≤ 1/4`), so
  `T1 + T2 ≤ (1-εT)(7/20)(q/s)` as in Region II.
Template: `Work.BoseKinLoc.Assembly.far_far_core`. -/
theorem region_far_far {K C q d s εT b : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hq : 0 ≤ q) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hsc : s ≤ cFS K C)
    (hε : 0 ≤ εT) (hεc : εT ≤ cFS K C) (hcpl : εT * s ≤ cFS K C * d)
    (hb : 0 ≤ b) (hb16 : b ≤ 1 / 16)
    (h1 : (5 / 6) * (2 * s)⁻¹ ≤ q) (h2 : (5 / 6) * (2 * (d * s))⁻¹ ≤ q) :
    (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        + b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2))
        + (1 - εT) * Work.BoseKinLoc.Assembly.tprR (2 * s) C q
        + εT * Work.BoseKinLoc.Assembly.tprR (2 * (d * s)) C q
      ≤ q ^ 2 := by
  have hcf4 : cFS K C ≤ 1 / 4 := cFS_le_quarter K C
  have hs4 : s ≤ 1 / 4 := le_trans hsc hcf4
  have hε4 : εT ≤ 1 / 4 := le_trans hεc hcf4
  have hmε : 0 ≤ 1 - εT := by linarith
  have hAc : (1 + K) / 2 * cFS K C ≤ 1 / 128 := half_one_add_mul_cFS_le K C hK hC
  -- ### the far branches
  have h2s : 0 < 2 * s := by linarith
  have h2ds : 0 < 2 * (d * s) := by positivity
  rw [Work.BoseKinLoc.Assembly.tprR_far_gen h2s h1,
    Work.BoseKinLoc.Assembly.tprR_far_gen h2ds h2,
    Work.BoseKinLoc.Assembly.two_two_inv s, Work.BoseKinLoc.Assembly.two_two_inv (d * s)]
  -- ### `T1 + T2 ≤ (7/20)(q/s)` (the Bogolubov pair)
  have hT1T2 : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
      + b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ (7 / 20) * (q / s) := by
    -- AM–GM: `q²/(1+d²q²) ≤ q/(2d)`
    have hAM : q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ q / (2 * d) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hq, sq_nonneg (d * q - 1)]
    have hT1a : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        ≤ (1 + K) / 2 * εT * (q / (2 * d)) := by
      have h := mul_le_mul_of_nonneg_left hAM (by positivity : (0 : ℝ) ≤ (1 + K) / 2 * εT)
      calc (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
          = (1 + K) / 2 * εT * (q ^ 2 / (1 + d ^ 2 * q ^ 2)) := by ring
        _ ≤ (1 + K) / 2 * εT * (q / (2 * d)) := h
    -- the coupling `εT · s ≤ c d`
    have hεd : εT / d ≤ cFS K C / s := by
      rw [div_le_div_iff₀ hd hs]; exact hcpl
    have hT1b : (1 + K) / 2 * εT * (q / (2 * d))
        ≤ (1 + K) / 2 * cFS K C * (q / (2 * s)) := by
      have h := mul_le_mul_of_nonneg_left hεd
        (by positivity : (0 : ℝ) ≤ (1 + K) / 2 * q / 2)
      calc (1 + K) / 2 * εT * (q / (2 * d)) = ((1 + K) / 2 * q / 2) * (εT / d) := by ring
        _ ≤ ((1 + K) / 2 * q / 2) * (cFS K C / s) := h
        _ = (1 + K) / 2 * cFS K C * (q / (2 * s)) := by ring
    have hT1c : (1 + K) / 2 * cFS K C * (q / (2 * s)) ≤ (1 / 256) * (q / s) := by
      have h := mul_le_mul_of_nonneg_right hAc (by positivity : (0 : ℝ) ≤ q / (2 * s))
      calc (1 + K) / 2 * cFS K C * (q / (2 * s)) ≤ (1 / 128) * (q / (2 * s)) := h
        _ = (1 / 256) * (q / s) := by ring
    -- the gap term
    have hT2 : b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ 1 / 8 := by
      have h2r : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
      rw [h2r]
      have hr : q ^ 2 / (q ^ 2 + 1 / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hr0 : (0 : ℝ) ≤ q ^ 2 / (q ^ 2 + 1 / 2) := by positivity
      have hb' : 2 * b ≤ 1 / 8 := by linarith
      have := mul_le_mul hb' hr hr0 (by norm_num : (0 : ℝ) ≤ 1 / 8)
      nlinarith [this]
    -- `q/s ≥ 20/3`
    have hqs : (20 : ℝ) / 3 ≤ q / s := by
      have he : (5 / 6) * (2 * (d * s))⁻¹ = 5 / (12 * d * s) := by field_simp; ring
      have hq' : 5 / (12 * d * s) ≤ q := by rw [← he]; exact h2
      have h5 : 5 ≤ 12 * d * s * q := by
        have hds : (0 : ℝ) < 12 * d * s := by positivity
        have := (div_le_iff₀ hds).mp hq'
        linarith
      have h1' : 5 / (12 * d * s ^ 2) ≤ q / s := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h5, hs.le]
      have h2' : (20 : ℝ) / 3 ≤ 5 / (12 * d * s ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hd1, hs4, hs.le, hd.le, sq_nonneg s]
      linarith
    have hfin : (1 / 256) * (q / s) + 1 / 8 ≤ (7 / 20) * (q / s) := by linarith [hqs]
    linarith [hT1a, hT1b, hT1c, hT2, hfin]
  -- ### `T3 + T4 ≤ q² - (1-εT)(7/20)(q/s) - εT(7/20)(q/(ds))`
  have hcut : (1 - εT) * (q - (4 * s)⁻¹) ^ 2 + εT * (q - (4 * (d * s))⁻¹) ^ 2
      ≤ q ^ 2 - (1 - εT) * ((7 / 20) * (q / s)) - εT * ((7 / 20) * (q / (d * s))) := by
    have hcut1 : (1 - εT) * (q - (4 * s)⁻¹) ^ 2
        ≤ (1 - εT) * (q ^ 2 - (7 / 20) * (q / s)) := by
      have ha : (0 : ℝ) < (4 * s)⁻¹ := by positivity
      have hqa : (5 / 3) * (4 * s)⁻¹ ≤ q := by
        have e : (5 / 6) * (2 * s)⁻¹ = (5 / 3) * (4 * s)⁻¹ := by ring
        rw [e] at h1; exact h1
      have hv : (7 / 20) * (q / s) = (7 / 5) * q * (4 * s)⁻¹ := by field_simp; ring
      have hcore : (q - (4 * s)⁻¹) ^ 2 ≤ q ^ 2 - (7 / 20) * (q / s) := by
        rw [hv]; nlinarith [ha, hqa]
      exact mul_le_mul_of_nonneg_left hcore hmε
    have hcut2 : εT * (q - (4 * (d * s))⁻¹) ^ 2
        ≤ εT * (q ^ 2 - (7 / 20) * (q / (d * s))) := by
      have ha : (0 : ℝ) < (4 * (d * s))⁻¹ := by positivity
      have hqa : (5 / 3) * (4 * (d * s))⁻¹ ≤ q := by
        have e : (5 / 6) * (2 * (d * s))⁻¹ = (5 / 3) * (4 * (d * s))⁻¹ := by ring
        rw [e] at h2; exact h2
      have hv : (7 / 20) * (q / (d * s)) = (7 / 5) * q * (4 * (d * s))⁻¹ := by
        field_simp; ring
      have hcore : (q - (4 * (d * s))⁻¹) ^ 2 ≤ q ^ 2 - (7 / 20) * (q / (d * s)) := by
        rw [hv]; nlinarith [ha, hqa]
      exact mul_le_mul_of_nonneg_left hcore hε
    linarith [hcut1, hcut2]
  -- ### `d ≤ 1` turns `q/s` into `q/(ds)`
  have hqds : (7 / 20) * (q / s)
      ≤ (1 - εT) * ((7 / 20) * (q / s)) + εT * ((7 / 20) * (q / (d * s))) := by
    have hqs' : q / s ≤ q / (d * s) := by
      rw [div_le_div_iff₀ hs (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ q * s)
      nlinarith [h1]
    have hm := mul_le_mul_of_nonneg_left hqs' (by positivity : (0 : ℝ) ≤ εT * (7 / 20))
    linarith [hm]
  linarith [hT1T2, hcut, hqds]

end Work.BoseFixKin.Assembly
