import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory intervalIntegral Set Real

namespace Commons.MeasureTheory.Integral

/-- For `x ≥ 0`, `(x + 1) ^ (1/3) - x ^ (1/3) ≤ 1`. -/
lemma rpow_one_third_succ_sub_le_one (x : ℝ) (hx : 0 ≤ x) :
    (x + 1) ^ (1 / 3 : ℝ) - x ^ (1 / 3 : ℝ) ≤ 1 := by
  have h := Real.rpow_add_le_add_rpow hx (zero_le_one : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
  rw [Real.one_rpow] at h
  linarith

/-- The value of `∫ v in a..b, v ^ (-(2/3))`. -/
lemma integral_rpow_neg_two_thirds (a b : ℝ) :
    ∫ v in a..b, v ^ (-(2 / 3) : ℝ) = 3 * (b ^ (1 / 3 : ℝ) - a ^ (1 / 3 : ℝ)) := by
  have h := integral_rpow (a := a) (b := b) (r := -(2 / 3 : ℝ)) (Or.inl (by norm_num))
  rw [h, show -(2 / 3 : ℝ) + 1 = 1 / 3 by norm_num]
  ring

/-- `u ↦ |u| ^ r` is interval integrable for `r > -1`, on `0..c` with `c ≥ 0`. -/
lemma intervalIntegrable_abs_rpow_of_nonneg (r : ℝ) (hr : -1 < r) (c : ℝ) (hc : 0 ≤ c) :
    IntervalIntegrable (fun u : ℝ => |u| ^ r) volume 0 c := by
  refine (intervalIntegrable_congr (f := fun u : ℝ => u ^ r)
    (g := fun u : ℝ => |u| ^ r) ?_).mp (intervalIntegrable_rpow' hr)
  intro u hu
  have hu0 : 0 ≤ u := by rw [uIoc_of_le hc] at hu; exact hu.1.le
  simp only [abs_of_nonneg hu0]

/-- `u ↦ |u| ^ r` is interval integrable for `r > -1`, on `c..0` with `c ≤ 0`. -/
lemma intervalIntegrable_abs_rpow_of_nonpos (r : ℝ) (hr : -1 < r) (c : ℝ) (hc : c ≤ 0) :
    IntervalIntegrable (fun u : ℝ => |u| ^ r) volume c 0 := by
  have h1 : IntervalIntegrable (fun u : ℝ => (-u) ^ r) volume c 0 := by
    have hbase : IntervalIntegrable (fun v : ℝ => v ^ r) volume (-c) 0 := intervalIntegrable_rpow' hr
    have hcomp := hbase.comp_sub_left 0
    simpa using hcomp
  refine (intervalIntegrable_congr (f := fun u : ℝ => (-u) ^ r)
    (g := fun u : ℝ => |u| ^ r) ?_).mp h1
  intro u hu
  have hu0 : u ≤ 0 := by rw [uIoc_of_le hc] at hu; exact hu.2
  simp only [abs_of_nonpos hu0]

/-- `u ↦ |u| ^ r` is interval integrable for `r > -1` on any interval. -/
lemma intervalIntegrable_abs_rpow (r : ℝ) (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => |u| ^ r) volume a b := by
  have aux : ∀ {a b : ℝ}, a ≤ b → IntervalIntegrable (fun u : ℝ => |u| ^ r) volume a b := by
    intro a b hab
    rcases le_or_gt 0 a with ha0 | ha0
    · exact (intervalIntegrable_abs_rpow_of_nonneg r hr b (le_trans ha0 hab)).mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le (le_trans ha0 hab)]
        exact Icc_subset_Icc_left ha0)
    · rcases le_or_gt b 0 with hb0 | hb0
      · exact (intervalIntegrable_abs_rpow_of_nonpos r hr a (le_trans hab hb0)).mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (le_of_lt ha0)]
          exact Icc_subset_Icc_right hb0)
      · exact (intervalIntegrable_abs_rpow_of_nonpos r hr a (le_of_lt ha0)).trans
          (intervalIntegrable_abs_rpow_of_nonneg r hr b (le_of_lt hb0))
  rcases le_total a b with hab | hba
  · exact aux hab
  · exact (aux hba).symm

/-- Pointwise rewriting of the integrand. -/
lemma rpow_two_thirds_inv_eq (t s : ℝ) :
    ((|t - s|) ^ (2 / 3 : ℝ))⁻¹ = |t - s| ^ (-(2 / 3) : ℝ) :=
  (Real.rpow_neg (abs_nonneg (t - s)) (2 / 3)).symm

theorem intervalIntegral_rpow_abs_sub_inv_le_six (s : ℝ) :
    ∫ t in (0 : ℝ)..1, ((|t - s|) ^ (2 / 3 : ℝ))⁻¹ ≤ 6 := by
  rw [integral_congr (fun t _ => rpow_two_thirds_inv_eq t s)]
  have hsub : ∫ t in (0 : ℝ)..1, |t - s| ^ (-(2 / 3) : ℝ)
      = ∫ u in (-s)..(1 - s), |u| ^ (-(2 / 3) : ℝ) := by
    have h := integral_comp_sub_right (fun u : ℝ => |u| ^ (-(2 / 3) : ℝ)) s (a := (0 : ℝ)) (b := 1)
    simpa using h
  rw [hsub]
  rcases le_or_gt s 0 with hs | hs
  · -- Case A : s ≤ 0
    have h1 : ∫ u in (-s)..(1 - s), |u| ^ (-(2 / 3) : ℝ)
        = ∫ u in (-s)..(1 - s), u ^ (-(2 / 3) : ℝ) := by
      apply integral_congr
      intro u hu
      rw [uIcc_of_le (by linarith : -s ≤ 1 - s)] at hu
      have hu0 : 0 ≤ u := le_trans (by linarith : (0 : ℝ) ≤ -s) hu.1
      simp only [abs_of_nonneg hu0]
    rw [h1, integral_rpow_neg_two_thirds]
    have h3 : (1 - s) ^ (1 / 3 : ℝ) - (-s) ^ (1 / 3 : ℝ) ≤ 1 := by
      have h := rpow_one_third_succ_sub_le_one (-s) (by linarith)
      simpa [sub_eq_add_neg, add_comm] using h
    linarith
  · rcases le_or_gt 1 s with hs1 | hs1
    · -- Case B : 1 ≤ s
      have h1 : ∫ u in (-s)..(1 - s), |u| ^ (-(2 / 3) : ℝ)
          = ∫ u in (-s)..(1 - s), (-u) ^ (-(2 / 3) : ℝ) := by
        apply integral_congr
        intro u hu
        rw [uIcc_of_le (by linarith : -s ≤ 1 - s)] at hu
        have hu0 : u ≤ 0 := le_trans hu.2 (by linarith : 1 - s ≤ 0)
        simp only [abs_of_nonpos hu0]
      rw [h1]
      have h2 : ∫ u in (-s)..(1 - s), (-u) ^ (-(2 / 3) : ℝ)
          = ∫ v in (s - 1)..s, v ^ (-(2 / 3) : ℝ) := by
        have h := integral_comp_neg (fun v : ℝ => v ^ (-(2 / 3) : ℝ)) (a := -s) (b := 1 - s)
        simpa using h
      rw [h2, integral_rpow_neg_two_thirds]
      have h3 : s ^ (1 / 3 : ℝ) - (s - 1) ^ (1 / 3 : ℝ) ≤ 1 := by
        have h := rpow_one_third_succ_sub_le_one (s - 1) (by linarith)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      linarith
    · -- Case C : 0 < s < 1
      have hsplit : ∫ u in (-s)..(1 - s), |u| ^ (-(2 / 3) : ℝ)
          = (∫ u in (-s)..0, |u| ^ (-(2 / 3) : ℝ))
            + ∫ u in (0 : ℝ)..(1 - s), |u| ^ (-(2 / 3) : ℝ) := by
        exact (integral_add_adjacent_intervals
          (intervalIntegrable_abs_rpow (-(2 / 3)) (by norm_num) (-s) 0)
          (intervalIntegrable_abs_rpow (-(2 / 3)) (by norm_num) 0 (1 - s))).symm
      have e1 : ∫ u in (-s)..0, |u| ^ (-(2 / 3) : ℝ) = 3 * s ^ (1 / 3 : ℝ) := by
        have h1 : ∫ u in (-s)..0, |u| ^ (-(2 / 3) : ℝ)
            = ∫ u in (-s)..0, (-u) ^ (-(2 / 3) : ℝ) := by
          apply integral_congr
          intro u hu
          rw [uIcc_of_le (by linarith : -s ≤ 0)] at hu
          have hu0 : u ≤ 0 := hu.2
          simp only [abs_of_nonpos hu0]
        rw [h1]
        have h2 : ∫ u in (-s)..0, (-u) ^ (-(2 / 3) : ℝ)
            = ∫ v in (0 : ℝ)..s, v ^ (-(2 / 3) : ℝ) := by
          have h := integral_comp_neg (fun v : ℝ => v ^ (-(2 / 3) : ℝ)) (a := -s) (b := 0)
          simpa using h
        rw [h2, integral_rpow_neg_two_thirds]
        rw [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
        ring
      have e2 : ∫ u in (0 : ℝ)..(1 - s), |u| ^ (-(2 / 3) : ℝ)
          = 3 * (1 - s) ^ (1 / 3 : ℝ) := by
        have h1 : ∫ u in (0 : ℝ)..(1 - s), |u| ^ (-(2 / 3) : ℝ)
            = ∫ u in (0 : ℝ)..(1 - s), u ^ (-(2 / 3) : ℝ) := by
          apply integral_congr
          intro u hu
          rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - s)] at hu
          have hu0 : 0 ≤ u := hu.1
          simp only [abs_of_nonneg hu0]
        rw [h1, integral_rpow_neg_two_thirds]
        rw [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
        ring
      rw [hsplit, e1, e2]
      have ha : s ^ (1 / 3 : ℝ) ≤ 1 := by
        have h := Real.rpow_le_rpow (le_of_lt hs) (le_of_lt hs1) (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rwa [Real.one_rpow] at h
      have hb : (1 - s) ^ (1 / 3 : ℝ) ≤ 1 := by
        have h := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 - s) (by linarith : 1 - s ≤ 1)
          (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rwa [Real.one_rpow] at h
      linarith

end Commons.MeasureTheory.Integral