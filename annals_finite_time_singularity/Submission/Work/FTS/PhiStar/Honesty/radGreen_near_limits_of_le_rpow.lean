import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.rgNearSetup
import Submission.Work.FTS.PhiStar.Honesty.rgNearDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem radGreen_near_limits_of_le_rpow {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    (hvy : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    Filter.Tendsto (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun z : ℝ => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by

  have hSpos : 0 < rgS α m := rgS_pos hα hα4 hm
  have hKpos : 0 < rgK α m := rgK_pos hα m
  have hp : 0 < rgP α m := rgP_pos hα hm
  have hpge : 8 ≤ rgP α m := rgP_ge hα hα4 hm
  have hp32 : (3 : ℝ) / 2 < rgP α m := by linarith
  have hA1pos : 0 < rgA1 α m := by
    rw [rgA1]
    have hq : 0 < rgQ α m := rgQ_pos hα m
    have hp3 : 0 < rgP α m - 3 / 2 := by linarith
    have ha : (0 : ℝ) < rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) :=
      div_pos (mul_pos hq (Real.rpow_pos_of_pos (by norm_num) _)) (by linarith)
    have hb : (0 : ℝ) < 2 ^ (rgQ α m + 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hc : (0 : ℝ) < rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) :=
      div_pos (mul_pos hp (Real.rpow_pos_of_pos (by norm_num) _)) hp3
    exact mul_pos hKpos (add_pos (add_pos (add_pos ha hb) hc) one_pos)
  have hA2nn : 0 ≤ rgA2 α m := by
    rw [rgA2]
    exact mul_nonneg hKpos.le (mul_nonneg hp.le (Real.rpow_pos_of_pos (by norm_num) _).le)
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖ < η
        ∧ ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2‖ < η := by
    intro η hη
    have hc1 : 0 < 2 * (rgK α m) ^ 2 * (rgS α m) ^ 2 :=
      mul_pos (mul_pos (by norm_num) (pow_pos hKpos 2)) (pow_pos hSpos 2)
    have hc2 : 0 < rgA1 α m * rgK α m * rgS α m :=
      mul_pos (mul_pos hA1pos hKpos) hSpos
    have hev1 : ∀ᶠ e : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        2 * (rgK α m) ^ 2 * (rgS α m) ^ 2 * e ^ 2 ≤ η / 4 := by
      have h := eventually_rpow_le (a := 2)
        (c := η / 4 / (2 * (rgK α m) ^ 2 * (rgS α m) ^ 2)) (by norm_num) (by positivity)
      filter_upwards [h] with e he
      rw [show e ^ (2 : ℕ) = e ^ (2 : ℝ) from (Real.rpow_natCast e 2).symm]
      calc 2 * (rgK α m) ^ 2 * (rgS α m) ^ 2 * e ^ (2 : ℝ)
          ≤ 2 * (rgK α m) ^ 2 * (rgS α m) ^ 2
              * (η / 4 / (2 * (rgK α m) ^ 2 * (rgS α m) ^ 2)) :=
            mul_le_mul_of_nonneg_left he hc1.le
        _ = η / 4 := by
            have hne : (2 * (rgK α m) ^ 2 * (rgS α m) ^ 2) ≠ 0 := ne_of_gt hc1
            field_simp
    have hev2 : ∀ᶠ e : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        rgA1 α m * rgK α m * rgS α m * e ^ 2 ≤ η / 4 := by
      have h := eventually_rpow_le (a := 2) (c := η / 4 / (rgA1 α m * rgK α m * rgS α m))
        (by norm_num) (by positivity)
      filter_upwards [h] with e he
      rw [show e ^ (2 : ℕ) = e ^ (2 : ℝ) from (Real.rpow_natCast e 2).symm]
      calc rgA1 α m * rgK α m * rgS α m * e ^ (2 : ℝ)
          ≤ rgA1 α m * rgK α m * rgS α m * (η / 4 / (rgA1 α m * rgK α m * rgS α m)) :=
            mul_le_mul_of_nonneg_left he hc2.le
        _ = η / 4 := by
            have hne : (rgA1 α m * rgK α m * rgS α m) ≠ 0 := ne_of_gt hc2
            field_simp
    obtain ⟨ε, ⟨hε1, hε2⟩, hεmem⟩ := ((hev1.and hev2).and self_mem_nhdsWithin).exists
    have hε0 : 0 < ε := hεmem
    obtain ⟨δ₀, hδ₀0, hvy₀⟩ := hvy ε hε0
    set δ : ℝ := min δ₀ 1 with hδdef
    have hδ0 : 0 < δ := lt_min hδ₀0 one_pos
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hvyδ : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2) :=
      fun t ht htδ => hvy₀ t ht (le_trans htδ (min_le_left _ _))
    have hcfg : 0 ≤ rgCF α m c δ := rgCF_nonneg (α := α) (m := m) (c := c) hδ0
    have hcfg1 : 1 ≤ rgCF α m c δ := by
      rw [rgCF]
      have h1 : (0 : ℝ) ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2 :=
        div_nonneg (integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
          (ae_of_all _ (fun x hx => div_nonneg (sq_nonneg _) (pow_nonneg hx.1.le 4)))))
          (by norm_num)
      have h2 : (0 : ℝ) ≤ (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2 :=
        div_nonneg (integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg _)) (by norm_num)
      have h3 : (0 : ℝ) ≤ δ ^ (-(2 * rgP α m + 1)) := Real.rpow_nonneg hδ0.le _
      linarith
    have hcfgpos : 0 < rgCF α m c δ := lt_of_lt_of_le one_pos hcfg1
    have hct : 0 < rgA1 α m * rgK α m * ε * rgCF α m c δ
        + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
        + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1 := by
      have h1 : 0 ≤ rgA1 α m * rgK α m * ε * rgCF α m c δ :=
        mul_nonneg (mul_nonneg (mul_nonneg hA1pos.le hKpos.le) hε0.le) hcfg
      have h2 : 0 ≤ rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA2nn hKpos.le) hcfg) hε0.le) hSpos.le
      have h3 : 0 ≤ rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 :=
        mul_nonneg (mul_nonneg hA2nn hKpos.le) (sq_nonneg _)
      linarith
    have ht1 : ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2 * (z ^ (rgP α m - 3 / 2)) ^ 2 < 3 * η / 4 := by
      have hpos : 0 < 2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2 :=
        mul_pos (mul_pos (by norm_num) (pow_pos hKpos 2)) (pow_pos hcfgpos 2)
      have h := eventually_rpow_le (a := (rgP α m - 3 / 2) * 2)
        (c := (3 * η / 8) / (2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2))
        (by linarith) (div_pos (by linarith) hpos)
      filter_upwards [h, self_mem_nhdsWithin] with z hz hzmem
      have hz0 : (0 : ℝ) < z := hzmem
      have hsq : (z ^ (rgP α m - 3 / 2)) ^ 2 = z ^ ((rgP α m - 3 / 2) * 2) := by
        rw [sq, ← Real.rpow_add hz0]
        congr 1
        ring
      rw [hsq]
      calc 2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2 * z ^ ((rgP α m - 3 / 2) * 2)
          ≤ 2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2
              * ((3 * η / 8) / (2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hpos.le
        _ = 3 * η / 8 := by
            have hne : (2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2) ≠ 0 := ne_of_gt hpos
            field_simp
        _ < 3 * η / 4 := by linarith
    have ht2 : ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (rgA1 α m * rgK α m * ε * rgCF α m c δ
          + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
          + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1) * z ^ (rgP α m - 3 / 2)
          < 3 * η / 4 := by
      have h := eventually_rpow_le (a := rgP α m - 3 / 2)
        (c := (3 * η / 8) / (rgA1 α m * rgK α m * ε * rgCF α m c δ
          + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
          + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1))
        (by linarith) (div_pos (by linarith) hct)
      filter_upwards [h] with z hz
      calc (rgA1 α m * rgK α m * ε * rgCF α m c δ
            + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
            + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1) * z ^ (rgP α m - 3 / 2)
          ≤ (rgA1 α m * rgK α m * ε * rgCF α m c δ
              + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
              + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1)
              * ((3 * η / 8) / (rgA1 α m * rgK α m * ε * rgCF α m c δ
                + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
                + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hz hct.le
        _ = 3 * η / 8 := by
            have hne : (rgA1 α m * rgK α m * ε * rgCF α m c δ
              + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
              + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1) ≠ 0 := ne_of_gt hct
            field_simp
        _ < 3 * η / 4 := by linarith
    have hevz1 : ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), z ≤ 1 :=
      mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds one_pos))
        (fun z hz => (le_of_lt (show z < 1 from hz) : z ≤ 1))
    have hevz2 : ∀ᶠ z : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 2 * z ≤ δ :=
      mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 2)))
        (fun z hz => by
          have hz' : z < δ / 2 := hz
          show 2 * z ≤ δ
          linarith)
    filter_upwards [ht1, ht2, hevz1, hevz2, self_mem_nhdsWithin] with z hz1 hz2 hzle h2z hz0
    have hval := radGreen_value_bound (m := m) (c := c) hα hα4 hm hδ0 hδ1 hε0.le hvyδ hnear hfar
      z hz0 h2z
    have hder := radGreen_deriv_bound (m := m) (c := c) hα hα4 hm hδ0 hδ1 hε0.le hvyδ hnear hfar
      z hz0 h2z
    have hz0' : (0 : ℝ) < z := hz0
    have hznn : (0 : ℝ) ≤ z := hz0'.le
    have hz3 : (0 : ℝ) < z ^ 3 := by positivity
    have hz2pos : (0 : ℝ) < z ^ 2 := by positivity
    have hz3ne : z ^ 3 ≠ 0 := ne_of_gt hz3
    have hznorm3 : ‖z ^ 3‖ = z ^ 3 := Real.norm_of_nonneg hz3.le
    have hznorm2 : ‖z ^ 2‖ = z ^ 2 := Real.norm_of_nonneg hz2pos.le
    -- the two key rpow identities
    have hzp : z ^ (rgP α m) = z ^ (rgP α m - 3 / 2) * z ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have hp32r : (z ^ ((3 : ℝ) / 2)) ^ 2 = z ^ (3 : ℝ) := by
      rw [sq, ← Real.rpow_add hz0]
      congr 1
      ring
    have hp32z : (z ^ ((3 : ℝ) / 2)) ^ 2 = z ^ 3 := by
      rw [hp32r]
      exact Real.rpow_natCast z 3
    have hsqid : (z ^ ((3 : ℝ) / 2)) ^ 2 / z ^ (3 : ℝ) = 1 := by
      rw [hp32r, ← Real.rpow_sub hz0, show (3 : ℝ) - 3 = 0 by norm_num, Real.rpow_zero]
    constructor
    · have h1 : ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖
          = ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ ^ 2 / z ^ 3 := by
        rw [norm_div, norm_pow, hznorm3]
      have h2 : (ε * rgS α m * z ^ ((3 : ℝ) / 2) + rgCF α m c δ * z ^ (rgP α m)) ^ 2 / z ^ 3
          = (ε * rgS α m + rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2 := by
        rw [hzp]
        rw [show ε * rgS α m * z ^ ((3 : ℝ) / 2)
              + rgCF α m c δ * (z ^ (rgP α m - 3 / 2) * z ^ ((3 : ℝ) / 2))
            = (ε * rgS α m + rgCF α m c δ * z ^ (rgP α m - 3 / 2)) * z ^ ((3 : ℝ) / 2)
            from by ring]
        rw [mul_pow]
        rw [show (ε * rgS α m + rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2
              * (z ^ ((3 : ℝ) / 2)) ^ 2 / z ^ 3
            = (ε * rgS α m + rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2
              * ((z ^ ((3 : ℝ) / 2)) ^ 2 / z ^ (3 : ℝ)) from by
            rw [show z ^ 3 = z ^ (3 : ℝ) from (Real.rpow_natCast z 3).symm]
            ring]
        rw [hsqid, mul_one]
      have h3 : (ε * rgS α m + rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2
          ≤ 2 * (ε * rgS α m) ^ 2
            + 2 * (rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2 := by
        nlinarith [sq_nonneg (ε * rgS α m - rgCF α m c δ * z ^ (rgP α m - 3 / 2))]
      calc ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖
          = ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ ^ 2 / z ^ 3 := h1
        _ ≤ (rgK α m * (ε * rgS α m * z ^ ((3 : ℝ) / 2)
              + rgCF α m c δ * z ^ (rgP α m))) ^ 2 / z ^ 3 := by
            apply div_le_div_of_nonneg_right _ hz3.le
            exact pow_le_pow_left₀ (norm_nonneg _) hval 2
        _ = (rgK α m) ^ 2
              * ((ε * rgS α m * z ^ ((3 : ℝ) / 2) + rgCF α m c δ * z ^ (rgP α m)) ^ 2
                / z ^ 3) := by
            rw [mul_pow]; ring
        _ = (rgK α m) ^ 2
              * (ε * rgS α m + rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2 := by rw [h2]
        _ ≤ (rgK α m) ^ 2
              * (2 * (ε * rgS α m) ^ 2
                + 2 * (rgCF α m c δ * z ^ (rgP α m - 3 / 2)) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (pow_pos hKpos 2).le
        _ = 2 * (rgK α m) ^ 2 * (rgS α m) ^ 2 * ε ^ 2
              + 2 * (rgK α m) ^ 2 * (rgCF α m c δ) ^ 2
                * (z ^ (rgP α m - 3 / 2)) ^ 2 := by ring
        _ < η / 4 + 3 * η / 4 := by linarith [hε1, hz1]
        _ = η := by ring
    · have h1 : ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2‖
          = ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z‖
              * ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ / z ^ 2 := by
        rw [norm_div, norm_mul, hznorm2]
        try ring
      -- the four elementary identities
      have I1 : rgA1 α m * ε * z ^ ((1 : ℝ) / 2) * (rgK α m * ε * rgS α m * z ^ ((3 : ℝ) / 2))
            / z ^ 2 = rgA1 α m * rgK α m * ε ^ 2 * rgS α m := by
        rw [show rgA1 α m * ε * z ^ ((1 : ℝ) / 2) * (rgK α m * ε * rgS α m * z ^ ((3 : ℝ) / 2))
              / z ^ 2
            = rgA1 α m * rgK α m * ε * ε * rgS α m
              * (z ^ ((1 : ℝ) / 2) * z ^ ((3 : ℝ) / 2) / z ^ 2) from by ring]
        rw [show z ^ 2 = z ^ (2 : ℝ) from (Real.rpow_natCast z 2).symm]
        rw [show z ^ ((1 : ℝ) / 2) * z ^ ((3 : ℝ) / 2) / z ^ (2 : ℝ) = 1 from by
          rw [← Real.rpow_add hz0, ← Real.rpow_sub hz0,
            show (1 : ℝ) / 2 + 3 / 2 - 2 = 0 by norm_num, Real.rpow_zero]]
        try ring
      have I2 : rgA1 α m * ε * z ^ ((1 : ℝ) / 2) * (rgK α m * rgCF α m c δ * z ^ (rgP α m))
            / z ^ 2 = rgA1 α m * rgK α m * ε * rgCF α m c δ * z ^ (rgP α m - 3 / 2) := by
        rw [show rgA1 α m * ε * z ^ ((1 : ℝ) / 2) * (rgK α m * rgCF α m c δ * z ^ (rgP α m))
              / z ^ 2
            = rgA1 α m * rgK α m * ε * rgCF α m c δ
              * (z ^ ((1 : ℝ) / 2) * z ^ (rgP α m) / z ^ 2) from by ring]
        rw [show z ^ 2 = z ^ (2 : ℝ) from (Real.rpow_natCast z 2).symm]
        rw [show z ^ ((1 : ℝ) / 2) * z ^ (rgP α m) / z ^ (2 : ℝ) = z ^ (rgP α m - 3 / 2) from by
          rw [← Real.rpow_add hz0, ← Real.rpow_sub hz0]
          congr 1
          ring]
        try ring
      have I3 : rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1)
            * (rgK α m * ε * rgS α m * z ^ ((3 : ℝ) / 2)) / z ^ 2
          = rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m * z ^ (rgP α m - 3 / 2) := by
        rw [show rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1)
              * (rgK α m * ε * rgS α m * z ^ ((3 : ℝ) / 2)) / z ^ 2
            = rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
              * (z ^ (rgP α m - 1) * z ^ ((3 : ℝ) / 2) / z ^ 2) from by ring]
        rw [show z ^ 2 = z ^ (2 : ℝ) from (Real.rpow_natCast z 2).symm]
        rw [show z ^ (rgP α m - 1) * z ^ ((3 : ℝ) / 2) / z ^ (2 : ℝ)
              = z ^ (rgP α m - 3 / 2) from by
          rw [← Real.rpow_add hz0, ← Real.rpow_sub hz0]
          congr 1
          ring]
        try ring
      have I4 : rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1)
            * (rgK α m * rgCF α m c δ * z ^ (rgP α m)) / z ^ 2
          = rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 * z ^ (2 * rgP α m - 3) := by
        rw [show rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1)
              * (rgK α m * rgCF α m c δ * z ^ (rgP α m)) / z ^ 2
            = rgA2 α m * rgK α m * (rgCF α m c δ * rgCF α m c δ)
              * (z ^ (rgP α m - 1) * z ^ (rgP α m) / z ^ 2) from by ring]
        rw [show z ^ 2 = z ^ (2 : ℝ) from (Real.rpow_natCast z 2).symm]
        rw [show z ^ (rgP α m - 1) * z ^ (rgP α m) / z ^ (2 : ℝ) = z ^ (2 * rgP α m - 3) from by
          rw [← Real.rpow_add hz0, ← Real.rpow_sub hz0]
          congr 1
          ring]
        rw [sq]
        try ring
      have he4 : z ^ (2 * rgP α m - 3) ≤ z ^ (rgP α m - 3 / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hz0 hzle (by linarith)
      have h6 : rgA1 α m * rgK α m * ε ^ 2 * rgS α m ≤ η / 4 := by
        rw [show rgA1 α m * rgK α m * ε ^ 2 * rgS α m
              = rgA1 α m * rgK α m * rgS α m * ε ^ 2 from by ring]
        exact hε2
      calc ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2‖
          = ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z‖
              * ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ / z ^ 2 := h1
        _ ≤ (rgA1 α m * ε * z ^ ((1 : ℝ) / 2) + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1))
              * (rgK α m * (ε * rgS α m * z ^ ((3 : ℝ) / 2)
                + rgCF α m c δ * z ^ (rgP α m))) / z ^ 2 := by
            apply div_le_div_of_nonneg_right _ hz2pos.le
            refine mul_le_mul hder hval (norm_nonneg _) ?_
            exact add_nonneg (mul_nonneg (mul_nonneg hA1pos.le hε0.le) (Real.rpow_nonneg hznn _))
              (mul_nonneg (mul_nonneg hA2nn hcfg) (Real.rpow_nonneg hznn _))
        _ = rgA1 α m * ε * z ^ ((1 : ℝ) / 2) * (rgK α m * ε * rgS α m * z ^ ((3 : ℝ) / 2))
                / z ^ 2
              + rgA1 α m * ε * z ^ ((1 : ℝ) / 2) * (rgK α m * rgCF α m c δ * z ^ (rgP α m))
                / z ^ 2
              + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1)
                * (rgK α m * ε * rgS α m * z ^ ((3 : ℝ) / 2)) / z ^ 2
              + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1)
                * (rgK α m * rgCF α m c δ * z ^ (rgP α m)) / z ^ 2 := by ring
        _ = rgA1 α m * rgK α m * ε ^ 2 * rgS α m
              + rgA1 α m * rgK α m * ε * rgCF α m c δ * z ^ (rgP α m - 3 / 2)
              + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m * z ^ (rgP α m - 3 / 2)
              + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 * z ^ (2 * rgP α m - 3) := by
            rw [I1, I2, I3, I4]
        _ ≤ rgA1 α m * rgK α m * ε ^ 2 * rgS α m
              + (rgA1 α m * rgK α m * ε * rgCF α m c δ
                + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
                + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2) * z ^ (rgP α m - 3 / 2) := by
            have hA2nn' : 0 ≤ rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 :=
              mul_nonneg (mul_nonneg hA2nn hKpos.le) (sq_nonneg _)
            have hstep1 : rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 * z ^ (2 * rgP α m - 3)
                ≤ rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 * z ^ (rgP α m - 3 / 2) :=
              mul_le_mul_of_nonneg_left he4 hA2nn'
            linarith [hstep1]
        _ ≤ rgA1 α m * rgK α m * ε ^ 2 * rgS α m
              + (rgA1 α m * rgK α m * ε * rgCF α m c δ
                + rgA2 α m * rgK α m * rgCF α m c δ * ε * rgS α m
                + rgA2 α m * rgK α m * (rgCF α m c δ) ^ 2 + 1) * z ^ (rgP α m - 3 / 2) := by
            have hzz : 0 ≤ z ^ (rgP α m - 3 / 2) := Real.rpow_nonneg hznn _
            nlinarith [hzz]
        _ < η / 4 + 3 * η / 4 := by linarith [h6, hz2]
        _ = η := by ring
  refine ⟨?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (Metric.nhds_basis_ball.tendsto_right_iff).mpr ?_
    intro η hη
    filter_upwards [key η hη] with z hz
    simpa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hz.1
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (Metric.nhds_basis_ball.tendsto_right_iff).mpr ?_
    intro η hη
    filter_upwards [key η hη] with z hz
    simpa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hz.2

end Work.FTS.PhiStar.Honesty
