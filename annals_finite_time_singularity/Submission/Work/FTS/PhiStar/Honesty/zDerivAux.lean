/-
Infrastructure for `Work.FTS.PhiStar.Honesty.zDeriv_radGreen_sq_w_sq_integrableOn`:
exponent/measurability facts, pointwise AM-GM bounds, integrability of the two Green integrands
`rgF1`, `rgF2` on the relevant intervals, the tail-splitting identity for `rgB`, and the a.e.
differentiability of the two Green branches `rgA` (`z * rgA' = -q rgG1 + c`) and `rgB`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Real

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 1600000

variable {α : ℝ} {m : ℕ} {c : ℝ → ℝ}

/-! ### exponent facts -/

lemma zgQ28 (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) :
    28 ≤ Work.FTS.EllExist.rgQ α m :=
  Work.FTS.EllExist.rgQ_ge (α := α) (m := m) hα hα4 hm

lemma zgP8 (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) :
    8 ≤ Work.FTS.EllExist.rgP α m :=
  Work.FTS.EllExist.rgP_ge (α := α) (m := m) hα hα4 hm

/-! ### measurability -/

lemma zgF1_meas {μ : Measure ℝ} (hc : AEMeasurable c μ) :
    AEMeasurable (Work.FTS.EllExist.rgF1 α m c) μ := by
  have h : AEMeasurable (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) μ :=
    hc.mul (by fun_prop)
  exact h

lemma zgF2_meas {μ : Measure ℝ} (hc : AEMeasurable c μ) :
    AEMeasurable (Work.FTS.EllExist.rgF2 α m c) μ := by
  have h : AEMeasurable (fun t : ℝ => c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) μ :=
    hc.mul (by fun_prop)
  exact h

/-! ### pointwise bounds -/

lemma zg_rpow_sub_two {t : ℝ} (ht : 0 < t) (s : ℝ) : t ^ (s - 2) = t ^ s / t ^ 2 := by
  rw [Real.rpow_sub ht]
  norm_num

lemma zg_rpow_sq {t : ℝ} (ht : 0 < t) (s : ℝ) : (t ^ s) ^ 2 = t ^ (2 * s) := by
  rw [sq, ← Real.rpow_add ht]
  congr 1
  ring

lemma zgF1_le_near (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) {t : ℝ}
    (ht0 : 0 < t) :
    ‖Work.FTS.EllExist.rgF1 α m c t‖
      ≤ 1 / 2 * ((c t) ^ 2 / t ^ 4) + 1 / 2 * t ^ (2 * Work.FTS.EllExist.rgQ α m + 2) := by
  have hpow : 0 ≤ t ^ (Work.FTS.EllExist.rgQ α m - 1) := Real.rpow_nonneg ht0.le _
  rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul, abs_of_nonneg hpow]
  have hdiv : t ^ (Work.FTS.EllExist.rgQ α m - 1)
      = t ^ (Work.FTS.EllExist.rgQ α m + 1) / t ^ 2 := by
    rw [show Work.FTS.EllExist.rgQ α m - 1
      = (Work.FTS.EllExist.rgQ α m + 1) - 2 by ring, zg_rpow_sub_two ht0]
  rw [show |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      = (|c t| / t ^ 2) * t ^ (Work.FTS.EllExist.rgQ α m + 1) from by rw [hdiv]; ring]
  have hle : (|c t| / t ^ 2) * t ^ (Work.FTS.EllExist.rgQ α m + 1)
      ≤ ((|c t| / t ^ 2) ^ 2 + (t ^ (Work.FTS.EllExist.rgQ α m + 1)) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|c t| / t ^ 2 - t ^ (Work.FTS.EllExist.rgQ α m + 1))]
  have h1 : (|c t| / t ^ 2) ^ 2 = (c t) ^ 2 / t ^ 4 := by
    rw [div_pow, sq_abs, show (t ^ 2) ^ 2 = t ^ 4 by ring]
  have h2 : (t ^ (Work.FTS.EllExist.rgQ α m + 1)) ^ 2
      = t ^ (2 * Work.FTS.EllExist.rgQ α m + 2) := by
    rw [zg_rpow_sq ht0]
    congr 1
    ring
  rw [h1, h2] at hle
  linarith [hle]

lemma zgF1_le_far {t : ℝ} (ht1 : 1 ≤ t) :
    ‖Work.FTS.EllExist.rgF1 α m c t‖
      ≤ 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (2 * Work.FTS.EllExist.rgQ α m - 2) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hpow : 0 ≤ t ^ (Work.FTS.EllExist.rgQ α m - 1) := Real.rpow_nonneg ht0.le _
  rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul, abs_of_nonneg hpow]
  have hle : |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      ≤ (|c t| ^ 2 + (t ^ (Work.FTS.EllExist.rgQ α m - 1)) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|c t| - t ^ (Work.FTS.EllExist.rgQ α m - 1))]
  have h1 : |c t| ^ 2 = (c t) ^ 2 := sq_abs _
  have h2 : (t ^ (Work.FTS.EllExist.rgQ α m - 1)) ^ 2
      = t ^ (2 * Work.FTS.EllExist.rgQ α m - 2) := by
    rw [zg_rpow_sq ht0]
    congr 1
    ring
  rw [h1, h2] at hle
  linarith [hle]

lemma zgF2_le_near {a : ℝ} {t : ℝ} (ht0 : 0 < t) (ha : 0 < a) (hat : a ≤ t)
    (hp : 1 ≤ Work.FTS.EllExist.rgP α m) :
    ‖Work.FTS.EllExist.rgF2 α m c t‖ ≤ 1 / 2 * ((c t) ^ 2 / t ^ 4)
      + 1 / 2 * a ^ (2 - 2 * Work.FTS.EllExist.rgP α m) := by
  have hnn : 0 ≤ t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := Real.rpow_nonneg ht0.le _
  rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF2, abs_mul, abs_of_nonneg hnn]
  have hdiv : t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
      = t ^ (1 - Work.FTS.EllExist.rgP α m) / t ^ 2 := by
    rw [show -(Work.FTS.EllExist.rgP α m) - 1
      = (1 - Work.FTS.EllExist.rgP α m) - 2 by ring, zg_rpow_sub_two ht0]
  rw [show |c t| * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
      = (|c t| / t ^ 2) * t ^ (1 - Work.FTS.EllExist.rgP α m) from by rw [hdiv]; ring]
  have hle : (|c t| / t ^ 2) * t ^ (1 - Work.FTS.EllExist.rgP α m)
      ≤ ((|c t| / t ^ 2) ^ 2 + (t ^ (1 - Work.FTS.EllExist.rgP α m)) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|c t| / t ^ 2 - t ^ (1 - Work.FTS.EllExist.rgP α m))]
  have h1 : (|c t| / t ^ 2) ^ 2 = (c t) ^ 2 / t ^ 4 := by
    rw [div_pow, sq_abs, show (t ^ 2) ^ 2 = t ^ 4 by ring]
  have h2 : (t ^ (1 - Work.FTS.EllExist.rgP α m)) ^ 2
      = t ^ (2 - 2 * Work.FTS.EllExist.rgP α m) := by
    rw [zg_rpow_sq ht0]
    congr 1
    ring
  have h3 : t ^ (2 - 2 * Work.FTS.EllExist.rgP α m)
      ≤ a ^ (2 - 2 * Work.FTS.EllExist.rgP α m) :=
    Real.rpow_le_rpow_of_nonpos ha hat (by linarith)
  rw [h1, h2] at hle
  linarith [hle, h3]

lemma zgF2_le_far {t : ℝ} (ht1 : 1 ≤ t) :
    ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hnn : 0 ≤ t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := Real.rpow_nonneg ht0.le _
  rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF2, abs_mul, abs_of_nonneg hnn]
  have hle : |c t| * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
      ≤ (|c t| ^ 2 + (t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|c t| - t ^ (-(Work.FTS.EllExist.rgP α m) - 1))]
  have h1 : |c t| ^ 2 = (c t) ^ 2 := sq_abs _
  have h2 : (t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) ^ 2
      = t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) := by
    rw [zg_rpow_sq ht0]
    congr 1
    ring
  rw [h1, h2] at hle
  linarith [hle]

/-! ### `rgF1` integrability -/

theorem zgF1_integrableOn_Ioo01 (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioo 0 1) := by
  have hexp : (-1 : ℝ) < 2 * Work.FTS.EllExist.rgQ α m + 2 := by
    have := zgQ28 (α := α) (m := m) hα hα4 hm; linarith
  have hpow : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (2 * Work.FTS.EllExist.rgQ α m + 2)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr hexp
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / 2 * ((c t) ^ 2 / t ^ 4)
        + 1 / 2 * t ^ (2 * Work.FTS.EllExist.rgQ α m + 2)) (Set.Ioo 0 1) :=
    (hnear.const_mul (1 / 2)).add (hpow.const_mul (1 / 2))
  refine Integrable.mono' hmaj ((zgF1_meas (α := α) (m := m) hc).restrict).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact zgF1_le_near hα hα4 hm ht.1

theorem zgF1_integrableOn_Ioc_one (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {y : ℝ} (hy : 1 ≤ y) :
    MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 1 y) := by
  have hsub : Set.Ioc (1 : ℝ) y ⊆ Set.Ioi 1 := fun t ht => ht.1
  have hsq : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc 1 y) :=
    hfar.mono_set hsub
  have hcont : ContinuousOn (fun t : ℝ => t ^ (2 * Work.FTS.EllExist.rgQ α m - 2))
      (Set.Icc (1 : ℝ) y) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos ht.1)))
  have hpow : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (2 * Work.FTS.EllExist.rgQ α m - 2)) (Set.Ioc 1 y) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (2 * Work.FTS.EllExist.rgQ α m - 2))
      (Set.Ioc 1 y) := (hsq.const_mul (1 / 2)).add (hpow.const_mul (1 / 2))
  refine Integrable.mono' hmaj ((zgF1_meas (α := α) (m := m) hc).restrict).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact zgF1_le_far ht.1.le

theorem zgF1_intervalIntegrable_zero (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) (n : ℕ) :
    IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0 : ℝ) ((n : ℝ) + 1) := by
  have h1 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc (0 : ℝ) 1) :=
    (zgF1_integrableOn_Ioo01 hα hα4 hm hc hnear).congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))).symm
  have h2 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c)
      (Set.Ioc (1 : ℝ) ((n : ℝ) + 1)) :=
    zgF1_integrableOn_Ioc_one hα hα4 hm hc hfar
      (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
  have hun : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc (1 : ℝ) ((n : ℝ) + 1)
      = Set.Ioc (0 : ℝ) ((n : ℝ) + 1) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h3, h4⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h4⟩
    · intro h
      by_cases h' : x ≤ 1
      · exact Or.inl ⟨h.1, h'⟩
      · exact Or.inr ⟨lt_of_not_ge h', h.2⟩
  have hu := h1.union h2
  rw [hun] at hu
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]
  exact hu

/-! ### `rgF2` integrability on intervals inside `(0,1]` and `(1,∞)` -/

theorem zgF2_integrableOn_Ioc_of_pos (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioc a b) := by
  have hp : 1 ≤ Work.FTS.EllExist.rgP α m := by
    have := zgP8 (α := α) (m := m) hα hα4 hm; linarith
  have hq1 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc (0 : ℝ) 1) :=
    hnear.congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))).symm
  by_cases hb : b ≤ 1
  · have hsub : Set.Ioc a b ⊆ Set.Ioc (0 : ℝ) 1 :=
      fun t ht => ⟨lt_trans ha ht.1, le_trans ht.2 hb⟩
    have hsq : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc a b) :=
      hq1.mono_set hsub
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 1 / 2 * a ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) (Set.Ioc a b) :=
      integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hmaj : MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / 2 * ((c t) ^ 2 / t ^ 4)
          + 1 / 2 * a ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) (Set.Ioc a b) :=
      (hsq.const_mul (1 / 2)).add hconst
    refine Integrable.mono' hmaj ((zgF2_meas (α := α) (m := m) hc).restrict).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact zgF2_le_near (lt_trans ha ht.1) ha ht.1.le hp
  · have hb1 : (1:ℝ) < b := lt_of_not_ge hb
    have hfar1 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc (1 : ℝ) b) :=
      hfar.mono_set (fun t ht => ht.1)
    have hcont : ContinuousOn (fun t : ℝ => t ^ (-2 * Work.FTS.EllExist.rgP α m - 2))
        (Set.Icc (1 : ℝ) b) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos ht.1)))
    have hpow : MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ (-2 * Work.FTS.EllExist.rgP α m - 2)) (Set.Ioc 1 b) :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hmajfar : MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (-2 * Work.FTS.EllExist.rgP α m - 2))
        (Set.Ioc (1 : ℝ) b) := (hfar1.const_mul (1 / 2)).add (hpow.const_mul (1 / 2))
    have hfarInt : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c)
        (Set.Ioc (1 : ℝ) b) := by
      refine Integrable.mono' hmajfar ((zgF2_meas (α := α) (m := m) hc).restrict).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact zgF2_le_far ht.1.le
    by_cases ha1 : a ≤ 1
    · have hsub : Set.Ioc a b ⊆ Set.Ioc a 1 ∪ Set.Ioc (1 : ℝ) b := by
        intro t ht
        by_cases h : t ≤ 1
        · exact Or.inl ⟨ht.1, h⟩
        · exact Or.inr ⟨lt_of_not_ge h, ht.2⟩
      have hnearInt : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioc a 1) := by
        have hsub2 : Set.Ioc a 1 ⊆ Set.Ioc (0 : ℝ) 1 :=
          fun t ht => ⟨lt_trans ha ht.1, ht.2⟩
        have hsq : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc a 1) :=
          hq1.mono_set hsub2
        have hconst : MeasureTheory.IntegrableOn
            (fun _ : ℝ => 1 / 2 * a ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) (Set.Ioc a 1) :=
          integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        have hmaj : MeasureTheory.IntegrableOn
            (fun t : ℝ => 1 / 2 * ((c t) ^ 2 / t ^ 4)
              + 1 / 2 * a ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) (Set.Ioc a 1) :=
          (hsq.const_mul (1 / 2)).add hconst
        refine Integrable.mono' hmaj ((zgF2_meas (α := α) (m := m) hc).restrict).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact zgF2_le_near (lt_trans ha ht.1) ha ht.1.le hp
      exact (hnearInt.union hfarInt).mono_set hsub
    · exact hfarInt.mono_set (fun t ht => ⟨lt_trans (lt_of_not_ge ha1) ht.1, ht.2⟩)

/-! ### `rgF2` integrable on `(1,∞)` and the tail-splitting identity for `rgB` -/

theorem zgF2_integrableOn_Ioi_one (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi 1) := by
  have hp : -2 * Work.FTS.EllExist.rgP α m - 2 < -1 := by
    have := zgP8 (α := α) (m := m) hα hα4 hm; linarith
  have hpow : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (-2 * Work.FTS.EllExist.rgP α m - 2)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt hp one_pos
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (-2 * Work.FTS.EllExist.rgP α m - 2))
      (Set.Ioi 1) := (hfar.const_mul (1 / 2)).add (hpow.const_mul (1 / 2))
  refine Integrable.mono' hmaj ((zgF2_meas (α := α) (m := m) hc).restrict).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact zgF2_le_far ht.le

theorem zgB_eq_const_sub (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {y : ℝ} (hy : 0 < y) :
    Work.FTS.EllExist.rgB α m c y
      = (∫ t in Set.Ioi (1 : ℝ), Work.FTS.EllExist.rgF2 α m c t)
        - ∫ t in (1 : ℝ)..y, Work.FTS.EllExist.rgF2 α m c t := by
  have hfarInt : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi 1) :=
    zgF2_integrableOn_Ioi_one hα hα4 hm hc hfar
  by_cases hy1 : (1 : ℝ) ≤ y
  · have hc1 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioc (1 : ℝ) y) :=
      zgF2_integrableOn_Ioc_of_pos hα hα4 hm hc hnear hfar (by norm_num)
    have hdisj : Disjoint (Set.Ioc (1 : ℝ) y) (Set.Ioi y) :=
      Set.disjoint_left.mpr fun t ht ht' => absurd ht' (not_lt.mpr ht.2)
    have hun : Set.Ioc (1 : ℝ) y ∪ Set.Ioi y = Set.Ioi (1 : ℝ) := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · linarith
        · linarith
      · intro h
        by_cases h' : t ≤ y
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (lt_of_not_ge h')
    have hIoiy : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi y) :=
      hfarInt.mono_set (Set.Ioi_subset_Ioi hy1)
    have hsum := setIntegral_union hdisj measurableSet_Ioi hc1 hIoiy
    rw [hun] at hsum
    rw [Work.FTS.EllExist.rgB, intervalIntegral.integral_of_le hy1]
    linarith [hsum]
  · have hc1 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioc y 1) :=
      zgF2_integrableOn_Ioc_of_pos hα hα4 hm hc hnear hfar hy
    have hdisj : Disjoint (Set.Ioc y 1) (Set.Ioi (1 : ℝ)) :=
      Set.disjoint_left.mpr fun t ht ht' => absurd ht' (not_lt.mpr ht.2)
    have hun : Set.Ioc y 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi y := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3) <;> linarith
      · intro h
        by_cases h' : t ≤ 1
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (lt_of_not_ge h')
    have hIoc : (∫ x in Set.Ioc y 1, Work.FTS.EllExist.rgF2 α m c x)
        = -∫ t in (1 : ℝ)..y, Work.FTS.EllExist.rgF2 α m c t := by
      rw [← intervalIntegral.integral_of_le (show y ≤ 1 from le_of_lt (not_le.mp hy1)),
        intervalIntegral.integral_symm]
    have hsum := setIntegral_union hdisj measurableSet_Ioi hc1 hfarInt
    rw [hun, hIoc] at hsum
    rw [Work.FTS.EllExist.rgB]
    linarith [hsum]

/-! ### a.e. differentiability of the two branches -/

lemma zg_nat_cast_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n

theorem zg_ae_hasDerivAt_rgA (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ᵐ x ∂volume, 0 < x → HasDerivAt (Work.FTS.EllExist.rgA α m c)
      (Work.FTS.EllExist.rgF1 α m c x) x := by
  have hper : ∀ n : ℕ, ∀ᵐ x : ℝ, x ∈ Set.uIcc (0 : ℝ) ((n : ℝ) + 1) →
      HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, Work.FTS.EllExist.rgF1 α m c t)
        (Work.FTS.EllExist.rgF1 α m c x) x := by
    intro n
    have h := (zgF1_intervalIntegrable_zero hα hα4 hm hc hnear hfar n).ae_hasDerivAt_integral
    filter_upwards [h] with x hx hxmem
    refine hx hxmem 0 ?_
    rw [Set.uIcc_of_le (by positivity)]
    exact ⟨le_refl 0, by positivity⟩
  filter_upwards [ae_all_iff.mpr hper] with x hx hxpos
  have hmem : x ∈ Set.uIcc (0 : ℝ) ((Nat.ceil x : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by positivity)]
    exact ⟨hxpos.le, by linarith [Nat.le_ceil x]⟩
  exact hx (Nat.ceil x) hmem

theorem zg_ae_hasDerivAt_rgB (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ᵐ x ∂volume, 0 < x → HasDerivAt (Work.FTS.EllExist.rgB α m c)
      (-(Work.FTS.EllExist.rgF2 α m c x)) x := by
  have hnearInt (n : ℕ) : IntervalIntegrable (Work.FTS.EllExist.rgF2 α m c) volume
      (1 / ((n : ℝ) + 1)) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by
      rw [div_le_one (by positivity)]
      linarith [zg_nat_cast_nonneg n])]
    exact zgF2_integrableOn_Ioc_of_pos hα hα4 hm hc hnear hfar (by positivity)
  have hfarInt (n : ℕ) : IntervalIntegrable (Work.FTS.EllExist.rgF2 α m c) volume
      1 ((n : ℝ) + 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [zg_nat_cast_nonneg n])]
    exact zgF2_integrableOn_Ioc_of_pos hα hα4 hm hc hnear hfar (by norm_num)
  have hmem1 (n : ℕ) : (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 1)) 1 := by
    rw [Set.uIcc_of_le (by
      rw [div_le_one (by positivity)]
      linarith [zg_nat_cast_nonneg n])]
    exact ⟨by
      rw [div_le_one (by positivity)]
      linarith [zg_nat_cast_nonneg n], le_refl 1⟩
  have hmem2 (n : ℕ) : (1 : ℝ) ∈ Set.uIcc (1 : ℝ) ((n : ℝ) + 2) := by
    rw [Set.uIcc_of_le (by linarith [zg_nat_cast_nonneg n])]
    exact ⟨le_refl 1, by linarith [zg_nat_cast_nonneg n]⟩
  have h1 : ∀ n : ℕ, ∀ᵐ x : ℝ, x ∈ Set.uIcc (1 / ((n : ℝ) + 1)) 1 →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.FTS.EllExist.rgF2 α m c t)
        (Work.FTS.EllExist.rgF2 α m c x) x := by
    intro n
    have h := (hnearInt n).ae_hasDerivAt_integral
    filter_upwards [h] with x hx hxmem
    exact hx hxmem 1 (hmem1 n)
  have h2 : ∀ n : ℕ, ∀ᵐ x : ℝ, x ∈ Set.uIcc (1 : ℝ) ((n : ℝ) + 2) →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.FTS.EllExist.rgF2 α m c t)
        (Work.FTS.EllExist.rgF2 α m c x) x := by
    intro n
    have h := (hfarInt n).ae_hasDerivAt_integral
    filter_upwards [h] with x hx hxmem
    exact hx hxmem 1 (hmem2 n)
  filter_upwards [(ae_all_iff.mpr h1).and (ae_all_iff.mpr h2)] with x hx hxpos
  obtain ⟨hx1, hx2⟩ := hx
  have hderiv : HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.FTS.EllExist.rgF2 α m c t)
      (Work.FTS.EllExist.rgF2 α m c x) x := by
    by_cases hxle : x ≤ 1
    · refine hx1 (Nat.ceil (1 / x)) ?_
      rw [Set.uIcc_of_le (by
        rw [div_le_one (by positivity)]
        linarith [zg_nat_cast_nonneg (Nat.ceil (1 / x))])]
      refine ⟨?_, hxle⟩
      have hpos : 0 < 1 / x := by positivity
      have hle : 1 / ((Nat.ceil (1 / x) : ℝ) + 1) ≤ 1 / (1 / x) := by
        apply one_div_le_one_div_of_le hpos
        linarith [Nat.le_ceil (1 / x)]
      rwa [one_div_one_div] at hle
    · refine hx2 (Nat.ceil x) ?_
      rw [Set.uIcc_of_le (by linarith [Nat.le_ceil x])]
      exact ⟨by linarith, by linarith [Nat.le_ceil x]⟩
  have hev : Work.FTS.EllExist.rgB α m c
      =ᶠ[𝓝 x] ((fun _ : ℝ => (∫ t in Set.Ioi (1 : ℝ), Work.FTS.EllExist.rgF2 α m c t))
        - fun y => ∫ t in (1 : ℝ)..y, Work.FTS.EllExist.rgF2 α m c t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
    exact zgB_eq_const_sub hα hα4 hm hc hnear hfar hy
  have hfin := ((hasDerivAt_const x (∫ t in Set.Ioi (1 : ℝ), Work.FTS.EllExist.rgF2 α m c t)).sub
    hderiv).congr_of_eventuallyEq hev
  simpa using hfin


end Work.FTS.PhiStar.Honesty
