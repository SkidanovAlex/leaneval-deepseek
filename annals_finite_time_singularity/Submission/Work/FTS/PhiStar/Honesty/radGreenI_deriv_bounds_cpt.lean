import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.rgiA_abs_le
import Submission.Work.FTS.PhiStar.Honesty.rgiB_abs_le
import Submission.Work.FTS.PhiStar.Honesty.rgiB_abs_le_small

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.PhiStar.Series (rgiA rgiB rgiF1 rgiF2 rgiK rgiSn rgiSp rgiD1)

set_option maxHeartbeats 2000000

/-! ## Auxiliary facts -/

/-- The explicit second derivative of the Green function (the derivative of `rgiD1`). -/
private def rgiD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m *
    (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
        + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
      + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
        + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))

private lemma hasDerivAt_rgiD1 {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hA : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiA α m c) (rgiF1 α m c z) z)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiB α m c) (-(rgiF2 α m c z)) z) :
    ∀ y : ℝ, 0 < y → HasDerivAt (rgiD1 α m c) (rgiD2 α m c y) y := by
  have hp1 : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => rgiSn α m * t ^ (rgiSn α m - 1))
        (rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) y := by
    intro y hy
    have h := (Real.hasDerivAt_rpow_const (x := y) (p := rgiSn α m - 1)
      (Or.inl (ne_of_gt hy))).const_mul (rgiSn α m)
    rwa [show rgiSn α m - 1 - 1 = rgiSn α m - 2 from by ring] at h
  have hp2 : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => rgiSp α m * t ^ (rgiSp α m - 1))
        (rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) y := by
    intro y hy
    have h := (Real.hasDerivAt_rpow_const (x := y) (p := rgiSp α m - 1)
      (Or.inl (ne_of_gt hy))).const_mul (rgiSp α m)
    rwa [show rgiSp α m - 1 - 1 = rgiSp α m - 2 from by ring] at h
  intro y hy
  have hres : HasDerivAt (fun t : ℝ => rgiK α m * ((rgiSn α m * t ^ (rgiSn α m - 1)) * rgiA α m c t
        + (rgiSp α m * t ^ (rgiSp α m - 1)) * rgiB α m c t))
      (rgiK α m * (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
          + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
        + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
          + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))) y :=
    (((hp1 y hy).mul (hA y hy)).add ((hp2 y hy).mul (hB y hy))).const_mul (rgiK α m)
  have hfun : (fun t : ℝ => rgiK α m * ((rgiSn α m * t ^ (rgiSn α m - 1)) * rgiA α m c t
      + (rgiSp α m * t ^ (rgiSp α m - 1)) * rgiB α m c t)) = rgiD1 α m c := rfl
  rw [hfun] at hres
  exact hres

/-- `rgiA` vanishes below the support of `c`. -/
private lemma rgiA_eq_zero_of_lt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {a y : ℝ}
    (hvan : ∀ t : ℝ, t < a → c t = 0) (hy : 0 < y) (hya : y < a) : rgiA α m c y = 0 := by
  have hzero : ∫ t in (0 : ℝ)..y, rgiF1 α m c t = ∫ t in (0 : ℝ)..y, (0 : ℝ) :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t ht => by
        rw [Set.uIoc_of_le hy.le] at ht
        have hlt : t < a := by linarith [ht.2]
        simp only [rgiF1, hvan t hlt, zero_mul])
  rw [rgiA, hzero, intervalIntegral.integral_zero]

/-- The arithmetic constant for the first conjunct. -/
private lemma key_const {α M : ℝ} {m : ℕ} (hα : 0 < α) (hm : 1 ≤ m) (hM : 0 ≤ M) :
    rgiK α m * (M / ((2 * (m : ℝ) + 5) / α) + M / (2 * (m : ℝ) / α))
      ≤ M / (m * (4 * (m : ℝ) + 5)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hαne : α ≠ 0 := ne_of_gt hα
  have h5 : (2 * (m : ℝ) + 5) ≠ 0 := by positivity
  have h2m : (2 * (m : ℝ)) ≠ 0 := by positivity
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have heq : rgiK α m * (M / ((2 * (m : ℝ) + 5) / α) + M / (2 * (m : ℝ) / α))
      = M / (4 * (m : ℝ) + 5) * (1 / (2 * (m : ℝ) + 5) + 1 / (2 * (m : ℝ))) := by
    simp only [rgiK]
    field_simp
  rw [heq]
  have hcoef : 1 / (2 * (m : ℝ) + 5) + 1 / (2 * (m : ℝ)) ≤ 1 / (m : ℝ) := by
    have h1 : 1 / (2 * (m : ℝ) + 5) ≤ 1 / (2 * (m : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have h2 : 1 / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 / (m : ℝ) := by
      rw [← add_div]
      field_simp
      norm_num
    linarith [h1, h2]
  calc M / (4 * (m : ℝ) + 5) * (1 / (2 * (m : ℝ) + 5) + 1 / (2 * (m : ℝ)))
      ≤ M / (4 * (m : ℝ) + 5) * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = M / (m * (4 * (m : ℝ) + 5)) := by
        field_simp

/-- The arithmetic constant for the second conjunct. -/
private lemma key_const2 {α M a : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) :
    rgiK α m * (M / a + M / a) = 2 * M / (α * (4 * (m : ℝ) + 5) * a) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  simp only [rgiK]
  field_simp
  ring

/-- The arithmetic constant for the small-`y` case of the third conjunct. -/
private lemma key_const3 {α M a : ℝ} {m : ℕ} (hα : 0 < α) (hm : 1 ≤ m)
    (hM : 0 ≤ M) (ha : 0 < a) :
    rgiK α m * (M * (2 * (m : ℝ) / α - 1) / a ^ 2) ≤ 10 * M / (α ^ 2 * a ^ 2) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hαne : α ≠ 0 := ne_of_gt hα
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  have hle : rgiK α m * (M * (2 * (m : ℝ) / α - 1) / a ^ 2)
      = M * (2 * (m : ℝ) - α) / (α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2) := by
    simp only [rgiK]
    field_simp
  rw [hle]
  have hden : 0 < α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2 := by positivity
  have hden2 : 0 < α ^ 2 * a ^ 2 := by positivity
  have hnum : M * (2 * (m : ℝ) - α) ≤ 10 * M * (4 * (m : ℝ) + 5) := by nlinarith [hM, hmR, hα]
  calc M * (2 * (m : ℝ) - α) / (α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2)
      ≤ (10 * M * (4 * (m : ℝ) + 5)) / (α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = 10 * M / (α ^ 2 * a ^ 2) := by
        field_simp

/-- The arithmetic constant for the large-`y` case of the third conjunct. -/
private lemma key_const4 {α M a : ℝ} {m : ℕ} (hα : 0 < α) (hM : 0 ≤ M) (ha : 0 < a) :
    rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2) ≤ 10 * M / (α ^ 2 * a ^ 2) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  have hle : rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2)
      = 2 * M / (α ^ 2 * a ^ 2) := by
    simp only [rgiK]
    field_simp
  rw [hle]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [hM]

theorem radGreenI_deriv_bounds_cpt {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ}
    (hm : 1 ≤ m) {c : ℝ → ℝ} {M a b : ℝ} (hM0 : 0 ≤ M) (ha : 0 < a)
    (hc : ContinuousOn c (Set.Ioi 0)) (hb : ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ t : ℝ, c t ≠ 0 → t ∈ Set.Icc a b)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    (∀ z : ℝ, 0 < z →
      |Work.FTS.PhiStar.Radial.radGreenI α m c z| ≤ M / (m * (4 * (m : ℝ) + 5))) ∧
    (∀ y : ℝ, 0 < y → |Work.FTS.PhiStar.Series.rgiD1 α m c y|
      ≤ 2 * M / (α * (4 * (m : ℝ) + 5) * a)) ∧
    (∀ y : ℝ, 0 < y → |deriv (Work.FTS.PhiStar.Series.rgiD1 α m c) y|
      ≤ 10 * M / (α ^ 2 * a ^ 2)) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hmm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : 0 < (2 * (m : ℝ) + 5) / α := div_pos (by positivity) hα
  have hq : 0 < 2 * (m : ℝ) / α := div_pos (by positivity) hα
  have hpne : (2 * (m : ℝ) + 5) / α ≠ 0 := ne_of_gt hp
  have hqne : 2 * (m : ℝ) / α ≠ 0 := ne_of_gt hq
  have hq1 : 1 ≤ 2 * (m : ℝ) / α := by rw [le_div_iff₀ hα]; nlinarith [hm1, hα4]
  have hq2 : 2 ≤ 2 * (m : ℝ) / α := by rw [le_div_iff₀ hα]; nlinarith [hm1, hα4]
  have hKpos : 0 < rgiK α m := by simp only [rgiK]; positivity
  have hKnonneg : 0 ≤ rgiK α m := hKpos.le
  have hvan : ∀ t : ℝ, t < a → c t = 0 := by
    intro t ht
    by_contra h
    have hmem := hsupp t h
    simp only [Set.mem_Icc] at hmem
    linarith [hmem.1]
  -- sign and absolute-value facts for the two indicial exponents
  have hSnneg : rgiSn α m < 0 := by
    simp only [rgiSn]
    exact div_neg_of_neg_of_pos (by linarith [hmm]) hα
  have hSn1neg : rgiSn α m - 1 < 0 := by linarith [hSnneg]
  have hSppos : 0 < rgiSp α m := by simp only [rgiSp]; exact hq
  have hSp1nn : 0 ≤ rgiSp α m - 1 := by simp only [rgiSp]; linarith [hq1]
  have hSp2nn : 0 ≤ rgiSp α m - 2 := by simp only [rgiSp]; linarith [hq2]
  have habsSn : |rgiSn α m| = (2 * (m : ℝ) + 5) / α := by
    rw [abs_of_neg hSnneg]
    simp only [rgiSn]
    ring
  have habsSp : |rgiSp α m| = 2 * (m : ℝ) / α := by
    rw [abs_of_pos hSppos]
    simp only [rgiSp]
  have habsSn1 : |rgiSn α m - 1| = (2 * (m : ℝ) + 5) / α + 1 := by
    rw [abs_of_neg hSn1neg]
    simp only [rgiSn]
    ring
  have habsSp1 : |rgiSp α m - 1| = 2 * (m : ℝ) / α - 1 := by
    rw [abs_of_nonneg hSp1nn]
    simp only [rgiSp]
  refine ⟨?_, ?_, ?_⟩
  · -- ### first conjunct
    intro z hz
    have hA := rgiA_abs_le (m := m) hα hM0 hb z hz
    have hB := rgiB_abs_le (m := m) hα hm hM0 hb z hz
    have hzSn : z ^ (rgiSn α m) * z ^ ((2 * (m : ℝ) + 5) / α) = 1 := by
      rw [← Real.rpow_add hz,
        show rgiSn α m + (2 * (m : ℝ) + 5) / α = 0 by simp only [rgiSn]; ring,
        Real.rpow_zero]
    have hzSp : z ^ (rgiSp α m) * z ^ (-(2 * (m : ℝ) / α)) = 1 := by
      rw [← Real.rpow_add hz,
        show rgiSp α m + (-(2 * (m : ℝ) / α)) = 0 by simp only [rgiSp]; ring,
        Real.rpow_zero]
    have hA' : z ^ (rgiSn α m) * |rgiA α m c z| ≤ M / ((2 * (m : ℝ) + 5) / α) := by
      calc z ^ (rgiSn α m) * |rgiA α m c z|
          ≤ z ^ (rgiSn α m)
              * (M * z ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α)) :=
            mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hz.le _)
        _ = (z ^ (rgiSn α m) * z ^ ((2 * (m : ℝ) + 5) / α))
              * (M / ((2 * (m : ℝ) + 5) / α)) := by ring
        _ = M / ((2 * (m : ℝ) + 5) / α) := by rw [hzSn, one_mul]
    have hB' : z ^ (rgiSp α m) * |rgiB α m c z| ≤ M / (2 * (m : ℝ) / α) := by
      calc z ^ (rgiSp α m) * |rgiB α m c z|
          ≤ z ^ (rgiSp α m) * (M * z ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
            mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hz.le _)
        _ = (z ^ (rgiSp α m) * z ^ (-(2 * (m : ℝ) / α))) * (M / (2 * (m : ℝ) / α)) := by ring
        _ = M / (2 * (m : ℝ) / α) := by rw [hzSp, one_mul]
    simp only [Work.FTS.PhiStar.Series.radGreenI_eq_rgi]
    calc |rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z + z ^ (rgiSp α m) * rgiB α m c z)|
        = rgiK α m * |z ^ (rgiSn α m) * rgiA α m c z + z ^ (rgiSp α m) * rgiB α m c z| := by
          rw [abs_mul, abs_of_pos hKpos]
      _ ≤ rgiK α m
            * (|z ^ (rgiSn α m) * rgiA α m c z| + |z ^ (rgiSp α m) * rgiB α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKnonneg
      _ = rgiK α m
            * (z ^ (rgiSn α m) * |rgiA α m c z| + z ^ (rgiSp α m) * |rgiB α m c z|) := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz _),
            abs_of_pos (Real.rpow_pos_of_pos hz _)]
      _ ≤ rgiK α m * (M / ((2 * (m : ℝ) + 5) / α) + M / (2 * (m : ℝ) / α)) :=
          mul_le_mul_of_nonneg_left (add_le_add hA' hB') hKnonneg
      _ ≤ M / (m * (4 * (m : ℝ) + 5)) := key_const hα hm hM0
  · -- ### second conjunct
    intro y hy
    have hA := rgiA_abs_le (m := m) hα hM0 hb y hy
    have hB := rgiB_abs_le (m := m) hα hm hM0 hb y hy
    have htermA : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y| ≤ M / a := by
      by_cases hya : y < a
      · rw [rgiA_eq_zero_of_lt hvan hy hya, mul_zero, abs_zero]
        exact div_nonneg hM0 ha.le
      · have hay : a ≤ y := not_lt.mp hya
        have hySn : y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α) = y ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hy]
          congr 1
          simp only [rgiSn]; ring
        have habs : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y|
            = ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1) * |rgiA α m c y| := by
          rw [abs_mul, abs_mul, habsSn, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1) * |rgiA α m c y|
            ≤ ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
                * (M * y ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α)) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
          _ = M * (y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α)) := by
              field_simp
              try ring
          _ = M * y ^ (-(1 : ℝ)) := by rw [hySn]
          _ = M / y := by rw [Real.rpow_neg hy.le (1 : ℝ), Real.rpow_one, div_eq_mul_inv]
          _ ≤ M / a := div_le_div_of_nonneg_left hM0 ha hay
    have htermB : |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y| ≤ M / a := by
      by_cases hya : y < a
      · have hB0 := rgiB_abs_le_small (m := m) hα hm hM0 ha hb hsupp y hy hya
        have hle1 : y ^ (rgiSp α m - 1) ≤ a ^ (rgiSp α m - 1) :=
          Real.rpow_le_rpow hy.le hya.le hSp1nn
        have h2 : a ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α)) = a ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add ha]
          congr 1
          simp only [rgiSp]; ring
        have habs : |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, habsSp, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
                * (M * a ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB0 (by positivity)
          _ = M * (y ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ ≤ M * a ^ (-(1 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hM0
              calc y ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α))
                  ≤ a ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α)) :=
                    mul_le_mul_of_nonneg_right hle1 (Real.rpow_nonneg ha.le _)
                _ = a ^ (-(1 : ℝ)) := h2
          _ = M / a := by rw [Real.rpow_neg ha.le (1 : ℝ), Real.rpow_one, div_eq_mul_inv]
      · have hay : a ≤ y := not_lt.mp hya
        have hySp : y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α)) = y ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hy]
          congr 1
          simp only [rgiSp]; ring
        have habs : |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, habsSp, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
                * (M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB (by positivity)
          _ = M * (y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ = M * y ^ (-(1 : ℝ)) := by rw [hySp]
          _ = M / y := by rw [Real.rpow_neg hy.le (1 : ℝ), Real.rpow_one, div_eq_mul_inv]
          _ ≤ M / a := div_le_div_of_nonneg_left hM0 ha hay
    rw [rgiD1]
    calc |rgiK α m * ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y)|
        = rgiK α m * |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y| := by
          rw [abs_mul, abs_of_pos hKpos]
      _ ≤ rgiK α m * (|(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y|
            + |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKnonneg
      _ ≤ rgiK α m * (M / a + M / a) :=
          mul_le_mul_of_nonneg_left (add_le_add htermA htermB) hKnonneg
      _ = 2 * M / (α * (4 * (m : ℝ) + 5) * a) := key_const2 hα ha
  · -- ### third conjunct
    intro y hy
    rw [(hasDerivAt_rgiD1 (α := α) (m := m) (c := c)
      (fun z hz => Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc h0 z hz)
      (fun z hz => Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc hinf z hz) y hy).deriv]
    have hA := rgiA_abs_le (m := m) hα hM0 hb y hy
    have hB := rgiB_abs_le (m := m) hα hm hM0 hb y hy
    have hySn2 : y ^ (rgiSn α m - 2) * y ^ ((2 * (m : ℝ) + 5) / α) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSn]; ring
    have hySn1 : y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α - 1) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSn]; ring
    have hySp2 : y ^ (rgiSp α m - 2) * y ^ (-(2 * (m : ℝ) / α)) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSp]; ring
    have hySp1 : y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α) - 1) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSp]; ring
    have ha2 : a ^ (-(2 : ℝ)) = 1 / a ^ 2 := by
      rw [Real.rpow_neg ha.le (2 : ℝ), Real.rpow_two, inv_eq_one_div]
    by_cases hya : y < a
    · -- small case: `y` is below the support
      have hA0 : rgiA α m c y = 0 := rgiA_eq_zero_of_lt hvan hy hya
      have hcy : c y = 0 := hvan y hya
      have hF1 : rgiF1 α m c y = 0 := by simp only [rgiF1, hcy, zero_mul]
      have hF2 : rgiF2 α m c y = 0 := by simp only [rgiF2, hcy, zero_mul]
      have hB0 := rgiB_abs_le_small (m := m) hα hm hM0 ha hb hsupp y hy hya
      have hD2 : rgiD2 α m c y
          = rgiK α m
              * ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y) := by
        simp only [rgiD2, hA0, hF1, hF2, mul_zero, add_zero, neg_zero, zero_add]
      rw [hD2]
      have hfac : y ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α)) ≤ a ^ (-(2 : ℝ)) := by
        have h2 : a ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α)) = a ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_add ha]
          congr 1
          simp only [rgiSp]; ring
        calc y ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α))
            ≤ a ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy.le hya.le hSp2nn)
                (Real.rpow_nonneg ha.le _)
          _ = a ^ (-(2 : ℝ)) := h2
      have hmid : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
          ≤ M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by
        have habs : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, abs_mul, habsSp, habsSp1,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * (M * a ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB0 (by positivity)
          _ = M * (2 * (m : ℝ) / α - 1)
                * (y ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ ≤ M * (2 * (m : ℝ) / α - 1) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hfac (mul_nonneg hM0 (by linarith [hq1]))
          _ = M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by rw [ha2]; ring
      calc |rgiK α m * ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y)|
          = rgiK α m
              * |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y| := by
            rw [abs_mul, abs_of_pos hKpos]
        _ ≤ rgiK α m * (M * (2 * (m : ℝ) / α - 1) / a ^ 2) :=
            mul_le_mul_of_nonneg_left hmid hKnonneg
        _ ≤ 10 * M / (α ^ 2 * a ^ 2) := key_const3 hα hm hM0 ha
    · -- large case: `a ≤ y`
      have hay : a ≤ y := not_lt.mp hya
      have hle2 : y ^ (-(2 : ℝ)) ≤ a ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha hay (by norm_num)
      have hT1 : |(rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y|
          ≤ M * ((2 * (m : ℝ) + 5) / α + 1) / a ^ 2 := by
        have habs : |(rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y|
            = ((2 * (m : ℝ) + 5) / α)
              * (((2 * (m : ℝ) + 5) / α + 1) * y ^ (rgiSn α m - 2))
              * |rgiA α m c y| := by
          rw [abs_mul, abs_mul, abs_mul, habsSn, habsSn1,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc ((2 * (m : ℝ) + 5) / α) * (((2 * (m : ℝ) + 5) / α + 1) * y ^ (rgiSn α m - 2))
              * |rgiA α m c y|
            ≤ ((2 * (m : ℝ) + 5) / α) * (((2 * (m : ℝ) + 5) / α + 1) * y ^ (rgiSn α m - 2))
              * (M * y ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α)) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
          _ = M * ((2 * (m : ℝ) + 5) / α + 1)
                * (y ^ (rgiSn α m - 2) * y ^ ((2 * (m : ℝ) + 5) / α)) := by
              field_simp
              try ring
          _ = M * ((2 * (m : ℝ) + 5) / α + 1) * y ^ (-(2 : ℝ)) := by rw [hySn2]
          _ ≤ M * ((2 * (m : ℝ) + 5) / α + 1) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (by positivity)
          _ = M * ((2 * (m : ℝ) + 5) / α + 1) / a ^ 2 := by rw [ha2]; ring
      have hT2 : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y|
          ≤ M * ((2 * (m : ℝ) + 5) / α) / a ^ 2 := by
        have habs : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y|
            = ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
              * (|c y| * y ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
          rw [abs_mul, abs_mul, habsSn, abs_of_pos (Real.rpow_pos_of_pos hy _), rgiF1, abs_mul,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
              * (|c y| * y ^ ((2 * (m : ℝ) + 5) / α - 1))
            ≤ ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
              * (M * y ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right (hb y) (Real.rpow_nonneg hy.le _)
          _ = M * ((2 * (m : ℝ) + 5) / α)
                * (y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α - 1)) := by ring
          _ = M * ((2 * (m : ℝ) + 5) / α) * y ^ (-(2 : ℝ)) := by rw [hySn1]
          _ ≤ M * ((2 * (m : ℝ) + 5) / α) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (by positivity)
          _ = M * ((2 * (m : ℝ) + 5) / α) / a ^ 2 := by rw [ha2]; ring
      have hT3 : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
          ≤ M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by
        have habs : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, abs_mul, habsSp, habsSp1,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * (M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB (by positivity)
          _ = M * (2 * (m : ℝ) / α - 1)
                * (y ^ (rgiSp α m - 2) * y ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ = M * (2 * (m : ℝ) / α - 1) * y ^ (-(2 : ℝ)) := by rw [hySp2]
          _ ≤ M * (2 * (m : ℝ) / α - 1) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (mul_nonneg hM0 (by linarith [hq1]))
          _ = M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by rw [ha2]; ring
      have hT4 : |(rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))|
          ≤ M * (2 * (m : ℝ) / α) / a ^ 2 := by
        have habs : |(rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))|
            = (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
              * (|c y| * y ^ (-(2 * (m : ℝ) / α) - 1)) := by
          rw [abs_mul, abs_mul, habsSp, abs_of_pos (Real.rpow_pos_of_pos hy _), abs_neg, rgiF2,
            abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
              * (|c y| * y ^ (-(2 * (m : ℝ) / α) - 1))
            ≤ (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
              * (M * y ^ (-(2 * (m : ℝ) / α) - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right (hb y) (Real.rpow_nonneg hy.le _)
          _ = M * (2 * (m : ℝ) / α)
                * (y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α) - 1)) := by ring
          _ = M * (2 * (m : ℝ) / α) * y ^ (-(2 : ℝ)) := by rw [hySp1]
          _ ≤ M * (2 * (m : ℝ) / α) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (by positivity)
          _ = M * (2 * (m : ℝ) / α) / a ^ 2 := by rw [ha2]; ring
      have hsum : |(rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y|
            + |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y|
            + |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
            + |(rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))|
          ≤ M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2 := by
        have harith : M * ((2 * (m : ℝ) + 5) / α + 1) / a ^ 2
              + M * ((2 * (m : ℝ) + 5) / α) / a ^ 2
              + M * (2 * (m : ℝ) / α - 1) / a ^ 2 + M * (2 * (m : ℝ) / α) / a ^ 2
            = M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2 := by ring
        linarith [hT1, hT2, hT3, hT4, harith]
      have e1 := abs_add_le ((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y)
        ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
      have e2 := abs_add_le ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y)
        ((rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y)))
      have e3 := abs_add_le (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y)
          + ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y))
        (((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y)
          + ((rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))
      have htri : |rgiD2 α m c y| ≤ rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2) := by
        simp only [rgiD2]
        rw [abs_mul, abs_of_pos hKpos]
        apply mul_le_mul_of_nonneg_left _ hKnonneg
        linarith [e1, e2, e3, hsum]
      calc |rgiD2 α m c y| ≤ rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2) := htri
        _ ≤ 10 * M / (α ^ 2 * a ^ 2) := key_const4 hα hM0 ha

end Work.FTS.PhiStar.Honesty
