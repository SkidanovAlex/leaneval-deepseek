import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.ClassC.HonestCut

/-! ## Elementary support facts

The source `c` of `radGreen_compact_source` is supported in `[1,2]`, so it vanishes
identically on `(0,1)` and on `(2,∞)`. -/

lemma rcs_c_eq_zero_of_lt_one {c : ℝ → ℝ}
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc 1 2 → c z = 0) {t : ℝ} (ht : t < 1) : c t = 0 :=
  hsupp t fun hmem => absurd (Set.mem_Icc.mp hmem).1 (not_le.mpr ht)

lemma rcs_c_eq_zero_of_gt_two {c : ℝ → ℝ}
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc 1 2 → c z = 0) {t : ℝ} (ht : 2 < t) : c t = 0 :=
  hsupp t fun hmem => absurd (Set.mem_Icc.mp hmem).2 (not_le.mpr ht)

/-- The weight `w z = (1+z)²/z²` satisfies `w² ≤ 16` on `[1,∞)`: indeed `w z ≤ 4` there. -/
lemma rcs_w_sq_le_sixteen {z : ℝ} (hz : 1 ≤ z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hw4 : Work.Spaces.w z ≤ 4 := by
    rw [Work.Spaces.w]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [sq_nonneg (z - 1)]
  have hwnn : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  nlinarith [hw4, hwnn]

theorem radGreen_compact_source {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0))
    (hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc 1 2 → c z = 0) :
    ContinuousOn c (Set.Ioi 0)
    ∧ (∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    ∧ (∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)
    ∧ MeasureTheory.IntegrableOn (fun z : ℝ => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  obtain ⟨M, hMnn, hMb⟩ := hM
  have hc0 : ContinuousOn c (Set.Ioi 0) := (hc 0).continuousOn
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc0.mono fun z hz => by simp only [Set.mem_Ioi] at hz ⊢; linarith
  -- the exponent of the two singular weights is `≤ 0`
  have hexp_nonpos : -(2 * (m : ℝ) / α) - 1 ≤ 0 := by
    have : 0 ≤ 2 * (m : ℝ) / α := div_nonneg (by positivity) hα.le
    linarith
  refine ⟨hc0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ## the decay `|c t| ≤ K/t` on `[1,∞)`
    refine ⟨2 * M + 1, by linarith, ?_⟩
    intro t ht1
    rcases le_or_gt t 2 with ht2 | ht2
    · have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have hMle : M ≤ (2 * M + 1) / t := by
        rw [le_div_iff₀ ht0]
        nlinarith [mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ 2 - t)]
      linarith [hMb t]
    · rw [rcs_c_eq_zero_of_gt_two hsupp ht2, abs_zero]
      exact div_nonneg (by linarith) (by linarith)
  · -- ## the vanishing rate `|c t| ≤ K t^p` on `(0,1]`
    refine ⟨M + 1, 2, by linarith, by norm_num, ?_⟩
    intro t ht0 ht1
    rcases lt_or_eq_of_le ht1 with h | h
    · rw [rcs_c_eq_zero_of_lt_one hsupp h, abs_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg ht0.le 2)
    · subst h
      rw [Real.one_rpow, mul_one]
      linarith [hMb 1]
  · -- ## `c · t^((2m+5)/α - 1)` is integrable on `(0,1)`, where `c ≡ 0`
    refine MeasureTheory.integrableOn_zero.congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp [rcs_c_eq_zero_of_lt_one hsupp ht.2]
  · -- ## `c · t^(-2m/α - 1)` is integrable on `(0,1)`, where `c ≡ 0`
    refine MeasureTheory.integrableOn_zero.congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp [rcs_c_eq_zero_of_lt_one hsupp ht.2]
  · -- ## `c · t^(-2m/α - 1)` is integrable on `(1,∞)` (support in `[1,2]`)
    have hdom : IntegrableOn (fun t : ℝ => (4 * M) * t ^ (-2 : ℝ)) (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul
        (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) (by norm_num)) (4 * M)
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · have hpow : ContinuousOn (fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) :=
        continuous_id.continuousOn.rpow_const fun t ht => Or.inl
          (ne_of_gt (by simp only [Set.mem_Ioi] at ht; linarith : (0 : ℝ) < t))
      exact (hc1.mul hpow).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have hpow_le : t ^ (-(2 * (m : ℝ) / α) - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos ht1 hexp_nonpos
      have hpow_nn : 0 ≤ t ^ (-(2 * (m : ℝ) / α) - 1) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow_nn]
      rcases le_or_gt t 2 with ht2 | ht2
      · have h1 : |c t| * t ^ (-(2 * (m : ℝ) / α) - 1) ≤ M := by
          have := mul_le_mul (hMb t) hpow_le hpow_nn hMnn
          simpa using this
        have hz2 : (1 / 4 : ℝ) ≤ t ^ (-2 : ℝ) := by
          have h := Real.rpow_le_rpow_of_nonpos ht0 ht2 (show (-2 : ℝ) ≤ 0 by norm_num)
          have h2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num
          rwa [h2] at h
        have h2 : M ≤ (4 * M) * t ^ (-2 : ℝ) := by
          have hprod : 0 ≤ M * (4 * t ^ (-2 : ℝ) - 1) :=
            mul_nonneg hMnn (by linarith)
          nlinarith [hprod]
        linarith
      · rw [rcs_c_eq_zero_of_gt_two hsupp ht2, abs_zero, zero_mul]
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt ht0) _)
  · -- ## `c²w²` is integrable on `(0,∞)`
    have hleft : IntegrableOn (fun z : ℝ => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1) := by
      refine MeasureTheory.integrableOn_zero.congr_fun ?_ measurableSet_Ioo
      intro z hz
      simp [rcs_c_eq_zero_of_lt_one hsupp hz.2]
    have hleft' : IntegrableOn (fun z : ℝ => (c z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (Set.Ioc 0 1) :=
      MeasureTheory.IntegrableOn.congr_set_ae hleft
        (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1)).symm
    have hright : IntegrableOn (fun z : ℝ => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
      have hdom : IntegrableOn (fun z : ℝ => (100 * M ^ 2) * z ^ (-2 : ℝ)) (Set.Ioi 1) :=
        MeasureTheory.Integrable.const_mul
          (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) (by norm_num)) _
      refine MeasureTheory.Integrable.mono' hdom ?_ ?_
      · have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
          have hw1 : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 1) := by
            unfold Work.Spaces.w
            refine ((continuous_const.add continuous_id).continuousOn.pow 2).div
              (continuous_id.continuousOn.pow 2) fun z hz => ?_
            have hz0 : 0 < z := by simp only [Set.mem_Ioi] at hz; linarith
            show z ^ 2 ≠ 0
            positivity
          exact hw1.pow 2
        exact ((hc1.pow 2).mul hw).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have hz1 : 1 ≤ z := le_of_lt hz
        have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        rcases le_or_gt z 2 with hz2 | hz2
        · have hcsq : c z ^ 2 ≤ M ^ 2 := by
            have h1 := abs_le.mp (hMb z)
            exact sq_le_sq' h1.1 h1.2
          have hwsq : (Work.Spaces.w z) ^ 2 ≤ 16 := rcs_w_sq_le_sixteen hz1
          have hzpow : (1 / 4 : ℝ) ≤ z ^ (-2 : ℝ) := by
            have h := Real.rpow_le_rpow_of_nonpos hz0 hz2 (show (-2 : ℝ) ≤ 0 by norm_num)
            have h2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num
            rwa [h2] at h
          have h1 : c z ^ 2 * (Work.Spaces.w z) ^ 2 ≤ M ^ 2 * 16 :=
            mul_le_mul hcsq hwsq (by positivity) (by positivity)
          have h2 : M ^ 2 * 16 ≤ (100 * M ^ 2) * z ^ (-2 : ℝ) := by
            have hprod : 0 ≤ M ^ 2 * (100 * z ^ (-2 : ℝ) - 16) :=
              mul_nonneg (sq_nonneg M) (by linarith)
            nlinarith [hprod]
          linarith
        · rw [rcs_c_eq_zero_of_gt_two hsupp hz2]
          have hzero : ((0 : ℝ) ^ 2) * (Work.Spaces.w z) ^ 2 = 0 := by ring
          rw [hzero]
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hz0) _)
    have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
      rw [Set.Ioc_union_Ioi (show (1 : ℝ) ≤ max 0 1 by norm_num)]
      norm_num
    rw [← hunion]
    exact hleft'.union hright

end Work.FTS.ClassC.HonestCut
