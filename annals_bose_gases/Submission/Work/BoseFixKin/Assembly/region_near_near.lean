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

/-- Arithmetic core of the region-I budget: from `s ≤ cFS K C` and `εT ≤ cFS K C`
(`cFS K C = min (1/4) (1/(64 (K+C+1)))`) one gets the three coefficient bounds
`(1+K)/2 · εT ≤ 1/128`, `8 C s³ ≤ 1/128` and `s ≤ 1/4`. -/
lemma cFS_coeff_bounds {K C s εT : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hs : 0 ≤ s)
    (hε : 0 ≤ εT) (hsc : s ≤ cFS K C) (hεc : εT ≤ cFS K C) :
    (1 + K) / 2 * εT ≤ 1 / 128 ∧ 8 * C * s ^ 3 ≤ 1 / 128 ∧ s ≤ 1 / 4 := by
  have hKC1 : 0 < K + C + 1 := by linarith
  have hsc4 : s ≤ 1 / 4 := le_trans hsc (min_le_left _ _)
  have hscd : s ≤ 1 / (64 * (K + C + 1)) := le_trans hsc (min_le_right _ _)
  have hεd : εT ≤ 1 / (64 * (K + C + 1)) := le_trans hεc (min_le_right _ _)
  -- multiply the `1/(64(K+C+1))` bounds through
  have hsden : s * (K + C + 1) ≤ 1 / 64 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (K + C + 1))).mp hscd
    nlinarith [h]
  have hεden : εT * (K + C + 1) ≤ 1 / 64 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (K + C + 1))).mp hεd
    nlinarith [h]
  have hCs : C * s ≤ 1 / 64 := by nlinarith [hsden, hs, hK]
  have hAε : (1 + K) / 2 * εT ≤ 1 / 128 := by nlinarith [hεden, hε, hK, hC.le]
  have hs2 : s ^ 2 ≤ 1 / 16 := by
    have h := pow_le_pow_left₀ hs hsc4 2
    norm_num at h
    linarith
  have hCs3 : 8 * C * s ^ 3 ≤ 1 / 128 := by
    have hprod : s ^ 2 * (C * s) ≤ (1 / 16) * (1 / 64) :=
      mul_le_mul hs2 hCs (mul_nonneg hC.le hs) (by norm_num)
    nlinarith [hprod]
  exact ⟨hAε, hCs3, hsc4⟩

/-- **Region I (both branches near) of the three-region budget for `core_budget_fs`.**
Both `tprR` are on the near (Taylor) branch, so `tprR (2s) C q = C (2s)³ q²` and
`tprR (2ds) C q = C (2ds)³ q²` (`Work.BoseKinLoc.Assembly.tprR_near`).  The claim is a
coefficient bound: with `A := (1+K)/2` one has `A εT ≤ 1/128` and `8 C s³ ≤ 1/128`
(because `cFS K C ≤ min (1/4) (1/(64(K+C+1)))` gives `s ≤ 1/4`, `C s ≤ 1/64`), and
`T1 ≤ A εT q²`, `T2 ≤ 4 b q² ≤ q²/4`, `T3 + T4 ≤ 8 C s³ q²`; the total coefficient
`1/128 + 1/4 + 1/128 < 1`.  Template: `Work.BoseKinLoc.Assembly.budget_near_near`. -/
theorem region_near_near {K C q d s εT b : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hq : 0 ≤ q) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hsc : s ≤ cFS K C)
    (hε : 0 ≤ εT) (hεc : εT ≤ cFS K C) (hcpl : εT * s ≤ cFS K C * d)
    (hb : 0 ≤ b) (hb16 : b ≤ 1 / 16)
    (h1 : ¬ ((5 / 6) * (2 * s)⁻¹ ≤ q)) (h2 : ¬ ((5 / 6) * (2 * (d * s))⁻¹ ≤ q)) :
    (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        + b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2))
        + (1 - εT) * Work.BoseKinLoc.Assembly.tprR (2 * s) C q
        + εT * Work.BoseKinLoc.Assembly.tprR (2 * (d * s)) C q
      ≤ q ^ 2 := by
  have hq2 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  -- both branches are the near (Taylor) branch
  have ht3 : Work.BoseKinLoc.Assembly.tprR (2 * s) C q = C * (2 * s) ^ 3 * q ^ 2 :=
    Work.BoseKinLoc.Assembly.tprR_near h1
  have ht4 : Work.BoseKinLoc.Assembly.tprR (2 * (d * s)) C q
      = C * (2 * (d * s)) ^ 3 * q ^ 2 :=
    Work.BoseKinLoc.Assembly.tprR_near h2
  rw [ht3, ht4]
  -- the three coefficient bounds
  obtain ⟨hAε, hCs3, hs4⟩ := cFS_coeff_bounds hK hC hs.le hε hsc hεc
  have h4b : 4 * b ≤ 1 / 4 := by linarith
  -- T1 ≤ ((1+K)/2 · εT) q² ≤ q²/128
  have hT1 : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
      ≤ (1 + K) / 2 * εT * q ^ 2 := by
    have hqdiv : q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ q ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + d ^ 2 * q ^ 2)]
      nlinarith [sq_nonneg q, sq_nonneg (d * q ^ 2)]
    calc (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        = (1 + K) / 2 * εT * (q ^ 2 / (1 + d ^ 2 * q ^ 2)) := by ring
      _ ≤ (1 + K) / 2 * εT * q ^ 2 :=
          mul_le_mul_of_nonneg_left hqdiv
            (mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + K) / 2) hε)
  have hT1f : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ q ^ 2 / 128 := by
    have h := mul_le_mul_of_nonneg_right hAε hq2
    linarith [hT1, h]
  -- T2 = 2b q²/(q²+1/2) ≤ 4 b q² ≤ q²/4
  have hT2 : b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ 4 * b * q ^ 2 := by
    have hdiv : q ^ 2 / (q ^ 2 + 1 / 2) ≤ 2 * q ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < q ^ 2 + 1 / 2)]
      nlinarith [sq_nonneg q]
    have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [h2]
    calc b * 2 * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ b * 2 * (2 * q ^ 2) :=
          mul_le_mul_of_nonneg_left hdiv (by linarith)
      _ = 4 * b * q ^ 2 := by ring
  have hT2f : b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ q ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right h4b hq2
    linarith [hT2, h]
  -- T3 + T4 ≤ 8 C s³ q² ≤ q²/128
  have hYleX : C * (2 * (d * s)) ^ 3 * q ^ 2 ≤ C * (2 * s) ^ 3 * q ^ 2 := by
    have hd3 : (2 * (d * s)) ^ 3 ≤ (2 * s) ^ 3 :=
      pow_le_pow_left₀ (by nlinarith [hd, hs]) (by nlinarith [hd, hs, hd1]) 3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hC.le) hq2
  have h34 : (1 - εT) * (C * (2 * s) ^ 3 * q ^ 2)
      + εT * (C * (2 * (d * s)) ^ 3 * q ^ 2) ≤ 8 * C * s ^ 3 * q ^ 2 := by
    have hX : C * (2 * s) ^ 3 * q ^ 2 = 8 * C * s ^ 3 * q ^ 2 := by ring
    have hle1 : εT * (C * (2 * (d * s)) ^ 3 * q ^ 2) ≤ εT * (8 * C * s ^ 3 * q ^ 2) := by
      rw [← hX]; exact mul_le_mul_of_nonneg_left hYleX hε
    have hle0 : (1 - εT) * (C * (2 * s) ^ 3 * q ^ 2)
        ≤ (1 - εT) * (8 * C * s ^ 3 * q ^ 2) := by rw [hX]
    nlinarith [hle0, hle1]
  have hT34f : (1 - εT) * (C * (2 * s) ^ 3 * q ^ 2)
      + εT * (C * (2 * (d * s)) ^ 3 * q ^ 2) ≤ q ^ 2 / 128 := by
    have h := mul_le_mul_of_nonneg_right hCs3 hq2
    linarith [h34, h]
  nlinarith [hT1f, hT2f, hT34f]

end Work.BoseFixKin.Assembly
