import Mathlib

/-!
# The gluing ramp of the odd window construction

We build an explicit `C^∞` function `gluePhi` used to glue the window solution `Z` of the
odd-dimensional Volterra system onto the semicircle chord function `profileX` on `(0, 1/2)`.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

noncomputable section

/-- The horizontal half-width of the gluing region. -/
def gW : ℝ := 1 / 4

/-- The smooth bump `ρ t = σ (50 t) σ (50 (1 - t))`. -/
def glueBump (t : ℝ) : ℝ :=
  Real.smoothTransition (50 * t) * Real.smoothTransition (50 * (1 - t))

lemma glueBump_nonneg (t : ℝ) : 0 ≤ glueBump t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma glueBump_le_one (t : ℝ) : glueBump t ≤ 1 := by
  have h1 : Real.smoothTransition (50 * t) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : Real.smoothTransition (50 * (1 - t)) ≤ 1 := Real.smoothTransition.le_one _
  have h3 : 0 ≤ Real.smoothTransition (50 * t) := Real.smoothTransition.nonneg _
  have h4 : 0 ≤ Real.smoothTransition (50 * (1 - t)) := Real.smoothTransition.nonneg _
  have h5 : glueBump t = Real.smoothTransition (50 * t) * Real.smoothTransition (50 * (1 - t)) := rfl
  rw [h5]
  nlinarith

lemma glueBump_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : glueBump t = 0 := by
  have h50 : 50 * t ≤ 0 := by linarith
  rw [glueBump, Real.smoothTransition.zero_of_nonpos h50, zero_mul]

lemma glueBump_zero_of_one_le {t : ℝ} (h : 1 ≤ t) : glueBump t = 0 := by
  have h50 : 50 * (1 - t) ≤ 0 := by linarith
  rw [glueBump, Real.smoothTransition.zero_of_nonpos h50, mul_zero]

lemma glueBump_one_of_mem {t : ℝ} (h1 : (1 : ℝ) / 50 ≤ t) (h2 : t ≤ 49 / 50) :
    glueBump t = 1 := by
  have h3 : (1 : ℝ) ≤ 50 * t := by linarith
  have h4 : (1 : ℝ) ≤ 50 * (1 - t) := by linarith
  rw [glueBump, Real.smoothTransition.one_of_one_le h3,
    Real.smoothTransition.one_of_one_le h4, mul_one]

lemma glueBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) glueBump := by
  unfold glueBump
  fun_prop

lemma glueBump_continuous : Continuous glueBump := glueBump_contDiff.continuous

lemma glueBump_intble (a b : ℝ) : IntervalIntegrable glueBump volume a b :=
  glueBump_continuous.intervalIntegrable a b

/-- The primitive of the bump. -/
def gluePrim (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, glueBump u

lemma gluePrim_hasDerivAt (x : ℝ) : HasDerivAt gluePrim (glueBump x) x :=
  intervalIntegral.integral_hasDerivAt_right (glueBump_intble 0 x)
    (glueBump_continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    glueBump_continuous.continuousAt

lemma gluePrim_deriv : deriv gluePrim = glueBump :=
  funext fun x => (gluePrim_hasDerivAt x).deriv

lemma gluePrim_contDiff : ContDiff ℝ (⊤ : ℕ∞) gluePrim := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (gluePrim_hasDerivAt x).differentiableAt, ?_⟩
  rw [gluePrim_deriv]
  exact glueBump_contDiff

lemma gluePrim_continuous : Continuous gluePrim := gluePrim_contDiff.continuous

lemma gluePrim_intble (a b : ℝ) : IntervalIntegrable gluePrim volume a b :=
  gluePrim_continuous.intervalIntegrable a b

lemma gluePrim_mono : Monotone gluePrim := by
  intro a b hab
  have h1 : IntervalIntegrable glueBump volume a b := glueBump_intble a b
  have h2 : IntervalIntegrable glueBump volume 0 a := glueBump_intble 0 a
  have h3 : (∫ u in (0 : ℝ)..b, glueBump u) =
      (∫ u in (0 : ℝ)..a, glueBump u) + ∫ u in a..b, glueBump u :=
    (intervalIntegral.integral_add_adjacent_intervals h2 h1).symm
  have h4 : 0 ≤ ∫ u in a..b, glueBump u :=
    intervalIntegral.integral_nonneg_of_forall hab (fun u => glueBump_nonneg u)
  have hb : gluePrim b = (∫ u in (0 : ℝ)..a, glueBump u) + ∫ u in a..b, glueBump u := by
    rw [gluePrim, h3]
  have ha : gluePrim a = ∫ u in (0 : ℝ)..a, glueBump u := rfl
  rw [hb, ha]
  linarith

lemma gluePrim_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : gluePrim t = 0 := by
  have h1 : (∫ u in (0 : ℝ)..t, glueBump u) = -∫ u in t..0, glueBump u :=
    (intervalIntegral.integral_symm t 0)
  have h2 : (∫ u in t..0, glueBump u) = ∫ u in t..0, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le h, Set.mem_Icc] at hu
    exact glueBump_zero_of_nonpos hu.2
  rw [gluePrim, h1, h2, intervalIntegral.integral_zero, neg_zero]

lemma gluePrim_nonneg {t : ℝ} (h : 0 ≤ t) : 0 ≤ gluePrim t := by
  have h0 : gluePrim 0 = 0 := gluePrim_zero_of_nonpos le_rfl
  have := gluePrim_mono h
  rwa [h0] at this

lemma gluePrim_nonneg_all (t : ℝ) : 0 ≤ gluePrim t := by
  by_cases h : t ≤ 0
  · rw [gluePrim_zero_of_nonpos h]
  · exact gluePrim_nonneg (by linarith)

lemma gluePrim_eq_of_one_le {t : ℝ} (h : 1 ≤ t) : gluePrim t = gluePrim 1 := by
  have h3 : (∫ u in (0 : ℝ)..t, glueBump u) =
      (∫ u in (0 : ℝ)..1, glueBump u) + ∫ u in 1..t, glueBump u :=
    (intervalIntegral.integral_add_adjacent_intervals (glueBump_intble 0 1) (glueBump_intble 1 t)).symm
  have h4 : (∫ u in (1 : ℝ)..t, glueBump u) = 0 := by
    have h5 : (∫ u in (1 : ℝ)..t, glueBump u) = ∫ u in (1 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le h, Set.mem_Icc] at hu
      exact glueBump_zero_of_one_le hu.1
    rw [h5, intervalIntegral.integral_zero]
  have hb : gluePrim t = (∫ u in (0 : ℝ)..1, glueBump u) + ∫ u in 1..t, glueBump u := by
    rw [gluePrim, h3]
  have ha : gluePrim 1 = ∫ u in (0 : ℝ)..1, glueBump u := rfl
  rw [hb, ha, h4, add_zero]

lemma gluePrim_le_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : gluePrim t ≤ t := by
  have h2 : (∫ u in (0 : ℝ)..t, glueBump u) ≤ ∫ u in (0 : ℝ)..t, (1 : ℝ) :=
    intervalIntegral.integral_mono_on h0 (glueBump_intble 0 t)
      (continuous_const.intervalIntegrable 0 t) (fun u _ => glueBump_le_one u)
  rw [integral_one] at h2
  have h3 : gluePrim t = ∫ u in (0 : ℝ)..t, glueBump u := rfl
  rw [h3]
  simpa using h2

lemma gluePrim_bounds_mid {t : ℝ} (h1 : (1 : ℝ) / 50 ≤ t) (h2 : t ≤ 49 / 50) :
    t - 1 / 50 ≤ gluePrim t ∧ gluePrim t ≤ t := by
  have h3 : gluePrim t = gluePrim (1 / 50) + (t - 1 / 50) := by
    have h4 : (∫ u in (0 : ℝ)..t, glueBump u) =
        (∫ u in (0 : ℝ)..(1 / 50), glueBump u) + ∫ u in (1 / 50)..t, glueBump u :=
      (intervalIntegral.integral_add_adjacent_intervals (glueBump_intble 0 (1/50)) (glueBump_intble (1/50) t)).symm
    have h5 : (∫ u in (1 / 50 : ℝ)..t, glueBump u) = ∫ u in (1 / 50 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le h1, Set.mem_Icc] at hu
      exact glueBump_one_of_mem hu.1 (le_trans hu.2 h2)
    have hb : gluePrim t = (∫ u in (0 : ℝ)..(1/50), glueBump u) + ∫ u in (1/50)..t, glueBump u := by
      rw [gluePrim, h4]
    have ha : gluePrim (1/50) = ∫ u in (0 : ℝ)..(1/50), glueBump u := rfl
    rw [hb, ha, h5, integral_one]
  have h6 : 0 ≤ gluePrim (1 / 50) := gluePrim_nonneg (by norm_num)
  have h7 : gluePrim (1 / 50) ≤ 1 / 50 := gluePrim_le_self (by norm_num) (by norm_num)
  rw [h3]
  constructor <;> linarith

lemma gluePrim_one_bounds : (24 : ℝ) / 25 ≤ gluePrim 1 ∧ gluePrim 1 ≤ 1 := by
  have h1 : gluePrim 1 = (∫ u in (0 : ℝ)..1, glueBump u) := rfl
  constructor
  · have h3 : (∫ u in (0 : ℝ)..1, glueBump u) =
        (∫ u in (0 : ℝ)..(1 / 50), glueBump u) + (∫ u in (1 / 50)..(49 / 50), glueBump u)
          + (∫ u in (49 / 50)..1, glueBump u) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (glueBump_intble 0 (1/50)) (glueBump_intble (1/50) (49/50)),
        intervalIntegral.integral_add_adjacent_intervals
          ((glueBump_intble 0 (1/50)).trans (glueBump_intble (1/50) (49/50))) (glueBump_intble (49/50) 1)]
    have h4 : 0 ≤ ∫ u in (0 : ℝ)..(1 / 50), glueBump u :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun u => glueBump_nonneg u)
    have h5 : 0 ≤ ∫ u in (49 / 50 : ℝ)..1, glueBump u :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun u => glueBump_nonneg u)
    have h6 : (24 : ℝ) / 25 ≤ ∫ u in (1 / 50 : ℝ)..(49 / 50), glueBump u := by
      have h7 : (∫ u in (1 / 50 : ℝ)..(49 / 50), (1 : ℝ)) ≤
          ∫ u in (1 / 50 : ℝ)..(49 / 50), glueBump u :=
        intervalIntegral.integral_mono_on (by norm_num)
          (continuous_const.intervalIntegrable _ _) (glueBump_intble _ _)
          (fun u hu => by
            rw [Set.mem_Icc] at hu
            rw [glueBump_one_of_mem hu.1 hu.2])
      rw [integral_one] at h7
      linarith
    rw [h1, h3]
    linarith
  · rw [h1]
    have h2 : (∫ u in (0 : ℝ)..1, glueBump u) ≤ ∫ u in (0 : ℝ)..1, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by norm_num) (glueBump_intble 0 1)
        (continuous_const.intervalIntegrable _ _) (fun u _ => glueBump_le_one u)
    rw [integral_one] at h2
    linarith

lemma gluePrim_int_Icc_ge : (24 : ℝ) / 25 * (24 / 25) / 2 ≤ (∫ t in (0 : ℝ)..1, gluePrim t) := by
  have hmono : (∫ t in (1 / 50 : ℝ)..(49 / 50), (t - 1 / 50)) ≤
      (∫ t in (1 / 50 : ℝ)..(49 / 50), gluePrim t) :=
    intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_id.sub continuous_const).intervalIntegrable _ _)
      (gluePrim_intble _ _)
      (fun u hu => by
        rw [Set.mem_Icc] at hu
        exact (gluePrim_bounds_mid hu.1 hu.2).1)
  have hval : (∫ t in (1 / 50 : ℝ)..(49 / 50), (t - 1 / 50)) = (24 : ℝ) / 25 * (24 / 25) / 2 := by
    rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => (1 / 50 : ℝ))
      (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      integral_id, intervalIntegral.integral_const]
    ring
  have hkey : (24 : ℝ) / 25 * (24 / 25) / 2 ≤ ∫ t in (1 / 50 : ℝ)..(49 / 50), gluePrim t := by
    rw [← hval]; exact hmono
  have hsplit : (∫ t in (0 : ℝ)..1, gluePrim t) =
      (∫ t in (0 : ℝ)..(1 / 50), gluePrim t) + (∫ t in (1 / 50 : ℝ)..(49 / 50), gluePrim t)
        + (∫ t in (49 / 50 : ℝ)..1, gluePrim t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (gluePrim_intble 0 (1/50)) (gluePrim_intble (1/50) (49/50)),
      intervalIntegral.integral_add_adjacent_intervals
        ((gluePrim_intble 0 (1/50)).trans (gluePrim_intble (1/50) (49/50))) (gluePrim_intble (49/50) 1)]
  have h4 : 0 ≤ ∫ t in (0 : ℝ)..(1 / 50), gluePrim t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun u => gluePrim_nonneg_all u)
  have h5 : 0 ≤ ∫ t in (49 / 50 : ℝ)..1, gluePrim t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun u => gluePrim_nonneg_all u)
  rw [hsplit]
  linarith

lemma gluePrim_int_Icc_le : (∫ t in (0 : ℝ)..1, gluePrim t) ≤ 1 / 2 := by
  have hmono : (∫ t in (0 : ℝ)..1, gluePrim t) ≤ ∫ t in (0 : ℝ)..1, t :=
    intervalIntegral.integral_mono_on (by norm_num) (gluePrim_intble 0 1)
      (continuous_id.intervalIntegrable _ _)
      (fun u hu => by
        rw [Set.mem_Icc] at hu
        exact gluePrim_le_self hu.1 hu.2)
  rw [integral_id] at hmono
  linarith

/-- The normalising integral `gI = ∫_0^2 gluePrim`. -/
def gI : ℝ := ∫ t in (0 : ℝ)..2, gluePrim t

lemma gI_eq : gI = (∫ t in (0 : ℝ)..1, gluePrim t) + gluePrim 1 := by
  have h1 : (∫ t in (0 : ℝ)..2, gluePrim t) =
      (∫ t in (0 : ℝ)..1, gluePrim t) + ∫ t in (1 : ℝ)..2, gluePrim t :=
    (intervalIntegral.integral_add_adjacent_intervals (gluePrim_intble 0 1) (gluePrim_intble 1 2)).symm
  have h2 : (∫ t in (1 : ℝ)..2, gluePrim t) = ∫ t in (1 : ℝ)..2, gluePrim 1 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2), Set.mem_Icc] at hu
    exact gluePrim_eq_of_one_le hu.1
  rw [gI, h1, h2, intervalIntegral.integral_const]
  ring

lemma gI_bounds : (71 : ℝ) / 50 ≤ gI ∧ gI ≤ 3 / 2 := by
  have h1 : (24 : ℝ) / 25 * (24 / 25) / 2 ≤ (∫ t in (0 : ℝ)..1, gluePrim t) :=
    gluePrim_int_Icc_ge
  have h2 : (∫ t in (0 : ℝ)..1, gluePrim t) ≤ 1 / 2 := gluePrim_int_Icc_le
  have h3 := gluePrim_one_bounds
  rw [gI_eq]
  constructor <;> linarith

lemma gI_pos : 0 < gI := by linarith [gI_bounds.1]

lemma gluePrim_int_nonneg {t : ℝ} (h : 0 ≤ t) : 0 ≤ ∫ u in (0 : ℝ)..t, gluePrim u :=
  intervalIntegral.integral_nonneg_of_forall h (fun u => gluePrim_nonneg_all u)

/-- Lower bound for `∫_0^t gluePrim` for `t ≥ 1/50`. -/
lemma gluePrim_int_ge_sq {t : ℝ} (h : (1 : ℝ) / 50 ≤ t) :
    (min t (49 / 50) - 1 / 50) ^ 2 / 2 ≤ ∫ u in (0 : ℝ)..t, gluePrim u := by
  set m := min t (49 / 50) with hm
  have hm1 : (1 : ℝ) / 50 ≤ m := le_min h (by norm_num)
  have hmt : m ≤ t := min_le_left _ _
  have hm2 : m ≤ 49 / 50 := min_le_right _ _
  have hsplit : (∫ u in (0 : ℝ)..t, gluePrim u) =
      (∫ u in (0 : ℝ)..m, gluePrim u) + ∫ u in m..t, gluePrim u :=
    (intervalIntegral.integral_add_adjacent_intervals (gluePrim_intble 0 m) (gluePrim_intble m t)).symm
  have hrest : 0 ≤ ∫ u in m..t, gluePrim u :=
    intervalIntegral.integral_nonneg_of_forall hmt (fun u => gluePrim_nonneg_all u)
  have hmono : (∫ u in (1 / 50 : ℝ)..m, (u - 1 / 50)) ≤
      (∫ u in (1 / 50 : ℝ)..m, gluePrim u) :=
    intervalIntegral.integral_mono_on hm1
      ((continuous_id.sub continuous_const).intervalIntegrable _ _)
      (gluePrim_intble _ _)
      (fun u hu => by
        rw [Set.mem_Icc] at hu
        exact (gluePrim_bounds_mid hu.1 (le_trans hu.2 hm2)).1)
  have hval : (∫ u in (1 / 50 : ℝ)..m, (u - 1 / 50)) = (m - 1 / 50) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => (1 / 50 : ℝ))
      (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      integral_id, intervalIntegral.integral_const]
    ring
  have hsplit2 : (∫ u in (0 : ℝ)..m, gluePrim u) =
      (∫ u in (0 : ℝ)..(1 / 50), gluePrim u) + ∫ u in (1 / 50 : ℝ)..m, gluePrim u :=
    (intervalIntegral.integral_add_adjacent_intervals (gluePrim_intble 0 (1/50)) (gluePrim_intble (1/50) m)).symm
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..(1 / 50), gluePrim u :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun u => gluePrim_nonneg_all u)
  have hkey : (m - 1 / 50) ^ 2 / 2 ≤ ∫ u in (1 / 50 : ℝ)..m, gluePrim u := by
    rw [← hval]; exact hmono
  rw [hsplit, hsplit2]
  linarith

lemma gluePrim_int_eq_zero_of_nonpos {t : ℝ} (h : t ≤ 0) :
    (∫ u in (0 : ℝ)..t, gluePrim u) = 0 := by
  have h1 : (∫ u in (0 : ℝ)..t, gluePrim u) = -∫ u in t..0, gluePrim u :=
    intervalIntegral.integral_symm t 0
  have h2 : (∫ u in t..0, gluePrim u) = 0 := by
    have h3 : (∫ u in t..0, gluePrim u) = ∫ u in t..0, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le h, Set.mem_Icc] at hu
      exact gluePrim_zero_of_nonpos hu.2
    rw [h3, intervalIntegral.integral_zero]
  rw [h1, h2, neg_zero]

lemma max0_mul_le {z w M K : ℝ} (hz : max 0 z ≤ M) (hw : w ≤ K) (hw0 : 0 ≤ w) :
    max 0 z * w ≤ M * K :=
  mul_le_mul hz hw hw0 (le_trans (le_max_left 0 z) hz)

lemma gluePrim_le_self_all {t : ℝ} (h : 0 ≤ t) : gluePrim t ≤ t := by
  rcases lt_or_ge t 1 with h1 | h1
  · exact gluePrim_le_self h h1.le
  · have h2 : gluePrim t = gluePrim 1 := gluePrim_eq_of_one_le h1
    have h3 : gluePrim 1 ≤ 1 := gluePrim_one_bounds.2
    linarith

lemma gW_pos : 0 < gW := by norm_num [gW]

lemma gW_gI_lo : (71 : ℝ) / 200 ≤ gW * gI := by
  have h : gW = 1 / 4 := rfl
  rw [h]; nlinarith [gI_bounds.1]

lemma gW_gI_hi : gW * gI ≤ 3 / 8 := by
  have h : gW = 1 / 4 := rfl
  rw [h]; nlinarith [gI_bounds.2]

lemma gW_gI_pos : 0 < gW * gI := mul_pos gW_pos gI_pos

lemma le_div_gW_of {c A d : ℝ} (hc : 0 ≤ c) (hd : (3 / 8) * c = d) (h : d ≤ A) :
    c ≤ A / (gW * gI) := by
  rw [le_div_iff₀ gW_gI_pos]
  rw [← hd] at h
  nlinarith [gW_gI_hi, hc, h]

lemma div_gW_le_of {c A d : ℝ} (hc : 0 ≤ c) (hd : c * ((71 : ℝ) / 200) = d) (h : A ≤ d) :
    A / (gW * gI) ≤ c := by
  rw [div_le_iff₀ gW_gI_pos]
  rw [← hd] at h
  nlinarith [gW_gI_lo, hc, h]

lemma div_gI_ge {S x : ℝ} (hx0 : 0 ≤ x) (hS : x ^ 2 / 2 ≤ S) : x ^ 2 / 3 ≤ S / gI := by
  rw [le_div_iff₀ gI_pos]
  nlinarith [hS, gI_bounds.2]

lemma div_gI_ge_of {S x d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ x) (hS : x ^ 2 / 2 ≤ S) :
    d ^ 2 / 3 ≤ S / gI := by
  have hx0 : 0 ≤ x := le_trans hd0 hd
  have hx2 : d ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have h := div_gI_ge hx0 hS
  linarith

/-- The core second-order bound, in the variable `t = 2 - 4 s`. -/
lemma gluePrim_cost_core {t : ℝ} (ht : t < 2) :
    (1 - gluePrim t / (gW * gI)) ^ 2
      + max 0 (2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI)
        * (16 * glueBump t / gI) ≤ 10 := by
  have hIlo : (71 : ℝ) / 50 ≤ gI := gI_bounds.1
  have hIhi : gI ≤ 3 / 2 := gI_bounds.2
  have hIpos : 0 < gI := gI_pos
  have hA0 : 0 ≤ gluePrim t := gluePrim_nonneg_all t
  have hP1 : glueBump t ≤ 1 := glueBump_le_one t
  have hw12 : 16 * glueBump t / gI ≤ 12 := by
    rw [div_le_iff₀ hIpos]; nlinarith
  have hw0 : 0 ≤ 16 * glueBump t / gI :=
    div_nonneg (mul_nonneg (by norm_num) (glueBump_nonneg t)) hIpos.le
  have hx0 : 0 ≤ gluePrim t / (gW * gI) := div_nonneg hA0 gW_gI_pos.le
  rcases lt_or_ge t 0 with ht0 | ht0
  · have hA : gluePrim t = 0 := gluePrim_zero_of_nonpos ht0.le
    have hS : (∫ u in (0 : ℝ)..t, gluePrim u) = 0 := gluePrim_int_eq_zero_of_nonpos ht0.le
    have hP : glueBump t = 0 := glueBump_zero_of_nonpos ht0.le
    rw [hA, hS, hP]
    norm_num
  · have hS0 : 0 ≤ ∫ u in (0 : ℝ)..t, gluePrim u := gluePrim_int_nonneg ht0
    have hdiv0 : 0 ≤ (∫ u in (0 : ℝ)..t, gluePrim u) / gI := div_nonneg hS0 hIpos.le
    rcases lt_or_ge t (1 / 50) with ht1 | ht1
    · -- 0 ≤ t < 1/50
      have hxhi : gluePrim t / (gW * gI) ≤ 4 / 71 :=
        div_gW_le_of (d := 1 / 50) (by norm_num) (by norm_num)
          (by linarith [gluePrim_le_self_all ht0, ht1])
      have hsq : (1 - gluePrim t / (gW * gI)) ^ 2 ≤ 1 := by nlinarith
      have hzm : max 0 (2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI) ≤ 81 / 200 :=
        max_le (by norm_num) (by linarith)
      have h := max0_mul_le hzm hw12 hw0
      linarith
    · rcases lt_or_ge t (1 / 2) with ht2 | ht2
      · -- 1/50 ≤ t < 1/2
        have hb := gluePrim_bounds_mid (t := t) ht1 (by linarith)
        have hxhi : gluePrim t / (gW * gI) ≤ 100 / 71 :=
          div_gW_le_of (d := 1 / 2) (by norm_num) (by norm_num) (by linarith [hb.2, ht2])
        have hsq : (1 - gluePrim t / (gW * gI)) ^ 2 ≤ 1 := by nlinarith
        have hzm : max 0 (2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI) ≤ 21 / 40 :=
          max_le (by norm_num) (by linarith)
        have h := max0_mul_le hzm hw12 hw0
        linarith
      · rcases lt_or_ge t (4 / 5) with ht3 | ht3
        · -- 1/2 ≤ t < 4/5
          have hb := gluePrim_bounds_mid (t := t) (by linarith) (by linarith)
          have hxlo : (32 : ℝ) / 25 ≤ gluePrim t / (gW * gI) :=
            le_div_gW_of (d := 12 / 25) (by norm_num) (by norm_num) (by linarith [hb.1, ht2])
          have hxhi : gluePrim t / (gW * gI) ≤ 160 / 71 :=
            div_gW_le_of (d := 4 / 5) (by norm_num) (by norm_num) (by linarith [hb.2, ht3])
          have hsq : (1 - gluePrim t / (gW * gI)) ^ 2 ≤ 7921 / 5041 := by nlinarith
          have hS0' : (t - 1 / 50) ^ 2 / 2 ≤ ∫ u in (0 : ℝ)..t, gluePrim u := by
            have h1 := gluePrim_int_ge_sq (t := t) (by linarith : (1 : ℝ)/50 ≤ t)
            have hmin : min t (49 / 50) = t := min_eq_left (by linarith)
            rwa [hmin] at h1
          have hSdiv : ((12 : ℝ) / 25) ^ 2 / 3 ≤ (∫ u in (0 : ℝ)..t, gluePrim u) / gI :=
            div_gI_ge_of (by norm_num) (by linarith) hS0'
          have hzle : 2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI ≤ 524 / 1000 := by
            linarith [hSdiv, ht3]
          have hzm : max 0 (2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI) ≤ 524 / 1000 :=
            max_le (by norm_num) hzle
          have h := max0_mul_le hzm hw12 hw0
          linarith
        · rcases lt_or_ge t (9 / 10) with ht4 | ht4
          · -- 4/5 ≤ t < 9/10
            have hb := gluePrim_bounds_mid (t := t) (by linarith) (by linarith)
            have hxlo : (52 : ℝ) / 25 ≤ gluePrim t / (gW * gI) :=
              le_div_gW_of (d := 39 / 50) (by norm_num) (by norm_num) (by linarith [hb.1, ht3])
            have hxhi : gluePrim t / (gW * gI) ≤ 180 / 71 :=
              div_gW_le_of (d := 9 / 10) (by norm_num) (by norm_num) (by linarith [hb.2, ht4])
            have hsq : (1 - gluePrim t / (gW * gI)) ^ 2 ≤ 11881 / 5041 := by nlinarith
            have hS0' : (t - 1 / 50) ^ 2 / 2 ≤ ∫ u in (0 : ℝ)..t, gluePrim u := by
              have h1 := gluePrim_int_ge_sq (t := t) (by linarith : (1 : ℝ)/50 ≤ t)
              have hmin : min t (49 / 50) = t := min_eq_left (by linarith)
              rwa [hmin] at h1
            have hSdiv : ((39 : ℝ) / 50) ^ 2 / 3 ≤ (∫ u in (0 : ℝ)..t, gluePrim u) / gI :=
              div_gI_ge_of (by norm_num) (by linarith) hS0'
            have hzle : 2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI ≤ 423 / 1000 := by
              linarith [hSdiv, ht4]
            have hzm : max 0 (2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI) ≤ 423 / 1000 :=
              max_le (by norm_num) hzle
            have h := max0_mul_le hzm hw12 hw0
            linarith
          · rcases lt_or_ge t 1 with ht5 | ht5
            · -- 9/10 ≤ t < 1
              have hgl : (22 : ℝ) / 25 ≤ gluePrim t := by
                have h1 := (gluePrim_bounds_mid (t := 9 / 10) (by norm_num) (by norm_num)).1
                have h2 : gluePrim (9 / 10) ≤ gluePrim t := gluePrim_mono ht4
                linarith
              have hxlo : (176 : ℝ) / 75 ≤ gluePrim t / (gW * gI) :=
                le_div_gW_of (d := 22 / 25) (by norm_num) (by norm_num) hgl
              have hxhi : gluePrim t / (gW * gI) ≤ 200 / 71 :=
                div_gW_le_of (d := 1) (by norm_num) (by norm_num)
                  (by linarith [gluePrim_le_self_all ht0, ht5])
              have hsq : (1 - gluePrim t / (gW * gI)) ^ 2 ≤ 16641 / 5041 := by nlinarith
              have hS0' : ((22 : ℝ) / 25) ^ 2 / 2 ≤ ∫ u in (0 : ℝ)..t, gluePrim u := by
                have h1 := gluePrim_int_ge_sq (t := t) (by linarith : (1 : ℝ)/50 ≤ t)
                have h2 : (22 : ℝ) / 25 ≤ min t (49 / 50) - 1 / 50 := by
                  have h3 : (9 : ℝ) / 10 ≤ min t (49 / 50) :=
                    le_min (by linarith) (by norm_num)
                  linarith
                have h4 : ((22 : ℝ) / 25) ^ 2 ≤ (min t (49 / 50) - 1 / 50) ^ 2 :=
                  pow_le_pow_left₀ (by norm_num) h2 2
                linarith
              have hSdiv : ((22 : ℝ) / 25) ^ 2 / 3 ≤ (∫ u in (0 : ℝ)..t, gluePrim u) / gI :=
                div_gI_ge (by norm_num) hS0'
              have hzle : 2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI ≤ 392 / 1000 := by
                linarith [hSdiv, ht5]
              have hzm : max 0 (2 / 5 + t / 4 - (∫ u in (0 : ℝ)..t, gluePrim u) / gI) ≤ 392 / 1000 :=
                max_le (by norm_num) hzle
              have h := max0_mul_le hzm hw12 hw0
              linarith
            · -- 1 ≤ t < 2
              have hA : gluePrim t = gluePrim 1 := gluePrim_eq_of_one_le ht5
              have hP : glueBump t = 0 := glueBump_zero_of_one_le ht5
              have hb := gluePrim_one_bounds
              rw [hA, hP]
              have hxlo : (64 : ℝ) / 25 ≤ gluePrim 1 / (gW * gI) :=
                le_div_gW_of (d := 24 / 25) (by norm_num) (by norm_num) (by linarith [hb.1])
              have hxhi : gluePrim 1 / (gW * gI) ≤ 200 / 71 :=
                div_gW_le_of (d := 1) (by norm_num) (by norm_num) (by linarith [hb.2])
              have hsq : (1 - gluePrim 1 / (gW * gI)) ^ 2 ≤ 16641 / 5041 := by nlinarith
              simp only [mul_zero, zero_div]
              linarith

/-- The normalised ramp, as a function of the *slope* variable. -/
def glueGG (δ : ℝ) : ℝ := (∫ u in (0 : ℝ)..(δ / gW), gluePrim u) / gI

/-- The gluing function `ψ`. -/
def gluePhi (s : ℝ) : ℝ := s + glueGG (1 / 2 - s)

lemma gluePhi_eq (s : ℝ) : gluePhi s = s + glueGG (1 / 2 - s) := rfl

lemma contDiff_prim_gluePrim :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ∫ u in (0 : ℝ)..t, gluePrim u) := by
  rw [contDiff_infty_iff_deriv]
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..t, gluePrim u)
      (gluePrim x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (gluePrim_intble 0 x)
      (gluePrim_continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      gluePrim_continuous.continuousAt
  refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
  have h : deriv (fun t : ℝ => ∫ u in (0 : ℝ)..t, gluePrim u) = gluePrim :=
    funext fun x => (hderiv x).deriv
  rw [h]
  exact gluePrim_contDiff

lemma glueGG_contDiff : ContDiff ℝ (⊤ : ℕ∞) glueGG := by
  unfold glueGG
  exact (contDiff_prim_gluePrim.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun δ : ℝ => δ / gW))).div_const gI

lemma gluePhi_contDiff : ContDiff ℝ (⊤ : ℕ∞) gluePhi := by
  unfold gluePhi
  exact contDiff_id.add (glueGG_contDiff.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 / 2 - s)))

lemma glueGG_mono : Monotone glueGG := by
  intro a b hab
  have hle : a / gW ≤ b / gW := div_le_div_of_nonneg_right hab gW_pos.le
  have h1 : IntervalIntegrable gluePrim volume (a / gW) (b / gW) := gluePrim_intble _ _
  have h2 : IntervalIntegrable gluePrim volume 0 (a / gW) := gluePrim_intble _ _
  have h3 : (∫ u in (0 : ℝ)..(b / gW), gluePrim u) =
      (∫ u in (0 : ℝ)..(a / gW), gluePrim u) + ∫ u in (a / gW)..(b / gW), gluePrim u :=
    (intervalIntegral.integral_add_adjacent_intervals h2 h1).symm
  have h4 : 0 ≤ ∫ u in (a / gW)..(b / gW), gluePrim u :=
    intervalIntegral.integral_nonneg_of_forall hle (fun u => gluePrim_nonneg_all u)
  have hb : glueGG b = ((∫ u in (0 : ℝ)..(a / gW), gluePrim u)
      + ∫ u in (a / gW)..(b / gW), gluePrim u) / gI := by
    rw [glueGG, h3]
  have ha : glueGG a = (∫ u in (0 : ℝ)..(a / gW), gluePrim u) / gI := rfl
  rw [hb, ha, div_le_div_iff_of_pos_right gI_pos]
  linarith

lemma glueGG_nonneg {δ : ℝ} (h : 0 ≤ δ) : 0 ≤ glueGG δ := by
  rw [glueGG]
  apply div_nonneg _ gI_pos.le
  exact intervalIntegral.integral_nonneg_of_forall (div_nonneg h gW_pos.le)
    (fun u => gluePrim_nonneg_all u)

lemma glueGG_nonneg_all (δ : ℝ) : 0 ≤ glueGG δ := by
  by_cases h : 0 ≤ δ
  · exact glueGG_nonneg h
  · have h2 : δ / gW ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) gW_pos.le
    rw [glueGG, gluePrim_int_eq_zero_of_nonpos h2, zero_div]

lemma glueGG_quarter : (1 : ℝ) / 4 < glueGG (1 / 4) := by
  have h1 : glueGG (1 / 4) = (∫ u in (0 : ℝ)..1, gluePrim u) / gI := by
    rw [glueGG]
    norm_num [gW]
  have h2 : (24 : ℝ) / 25 * (24 / 25) / 2 ≤ (∫ u in (0 : ℝ)..1, gluePrim u) := gluePrim_int_Icc_ge
  rw [h1, lt_div_iff₀ gI_pos]
  nlinarith [h2, gI_bounds.2]

lemma gluePhi_zero : gluePhi 0 = 1 := by
  have h : glueGG (1 / 2) = 1 := by
    rw [glueGG]
    have h2 : (1 : ℝ) / 2 / gW = 2 := by norm_num [gW]
    rw [h2]
    exact div_self (ne_of_gt gI_pos)
  rw [gluePhi]
  rw [show (1 : ℝ) / 2 - 0 = 1 / 2 by norm_num, h]
  norm_num

lemma gluePhi_of_half_le {s : ℝ} (h : 1 / 2 ≤ s) : gluePhi s = s := by
  have h2 : (1 / 2 - s) / gW ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) gW_pos.le
  have h3 : glueGG (1 / 2 - s) = 0 := by
    rw [glueGG, gluePrim_int_eq_zero_of_nonpos h2, zero_div]
  rw [gluePhi, h3, add_zero]

lemma gluePhi_gt_quarter {s : ℝ} (hs : 0 < s) : 1 / 4 < gluePhi s := by
  rcases le_total ((1 : ℝ) / 4) s with h | h
  · rcases lt_or_eq_of_le h with h' | h'
    · have h2 : 0 ≤ glueGG (1 / 2 - s) := glueGG_nonneg_all _
      rw [gluePhi]; linarith
    · have h4 : (1 : ℝ) / 4 < glueGG (1 / 2 - s) := by
        have h5 : (1 : ℝ) / 2 - s = 1 / 4 := by linarith
        rw [h5]; exact glueGG_quarter
      rw [gluePhi]; linarith
  · have h4 : (1 : ℝ) / 4 < glueGG (1 / 2 - s) := by
      have hm : glueGG (1 / 4) ≤ glueGG (1 / 2 - s) := glueGG_mono (by linarith)
      linarith [glueGG_quarter]
    rw [gluePhi]; linarith

lemma hasDerivAt_glueGG (δ : ℝ) :
    HasDerivAt glueGG (gluePrim (δ / gW) / (gW * gI)) δ := by
  have h1 : HasDerivAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, gluePrim x) (gluePrim (δ / gW)) (δ / gW) :=
    intervalIntegral.integral_hasDerivAt_right (gluePrim_intble 0 (δ / gW))
      (gluePrim_continuous.stronglyMeasurableAtFilter volume (𝓝 (δ / gW)))
      gluePrim_continuous.continuousAt
  have h2 : HasDerivAt (fun u : ℝ => u / gW) (1 / gW) δ := (hasDerivAt_id δ).div_const gW
  have h3 : HasDerivAt ((fun v : ℝ => ∫ x in (0 : ℝ)..v, gluePrim x) ∘ fun u : ℝ => u / gW)
      (gluePrim (δ / gW) * (1 / gW)) δ := HasDerivAt.comp δ h1 h2
  have h3a : ((fun v : ℝ => ∫ x in (0 : ℝ)..v, gluePrim x) ∘ fun u : ℝ => u / gW)
      = fun x : ℝ => ∫ u in (0 : ℝ)..x / gW, gluePrim u := by funext x; rfl
  rw [h3a] at h3
  have h3' : HasDerivAt (fun x : ℝ => (∫ u in (0 : ℝ)..x / gW, gluePrim u) / gI)
      ((gluePrim (δ / gW) * (1 / gW)) / gI) δ := h3.div_const gI
  have h4 : (gluePrim (δ / gW) * (1 / gW)) / gI = gluePrim (δ / gW) / (gW * gI) := by
    rw [gW]; ring
  rw [h4] at h3'
  exact h3'

lemma hasDerivAt_gluePhi (s : ℝ) :
    HasDerivAt gluePhi (1 - gluePrim ((1 / 2 - s) / gW) / (gW * gI)) s := by
  have h2 : HasDerivAt (fun u : ℝ => 1 / 2 - u) (-1) s := by
    have h := (hasDerivAt_const s (1 / 2 : ℝ)).sub (hasDerivAt_id s)
    have h' : ((fun x : ℝ => (1 : ℝ) / 2) - id) = fun u : ℝ => 1 / 2 - u := rfl
    rw [h'] at h
    have h'' : ((0 : ℝ) - 1) = -1 := by norm_num
    rw [h''] at h
    exact h
  have h3 : HasDerivAt (glueGG ∘ fun u : ℝ => 1 / 2 - u)
      (gluePrim ((1 / 2 - s) / gW) / (gW * gI) * (-1)) s :=
    HasDerivAt.comp s (hasDerivAt_glueGG (1 / 2 - s)) h2
  have h3a : (glueGG ∘ fun u : ℝ => 1 / 2 - u) = fun u : ℝ => glueGG (1 / 2 - u) := by
    funext x; rfl
  rw [h3a] at h3
  have h4 : HasDerivAt (fun u : ℝ => u + glueGG (1 / 2 - u))
      (1 + gluePrim ((1 / 2 - s) / gW) / (gW * gI) * (-1)) s :=
    (hasDerivAt_id s).add h3
  have h5 : (1 + gluePrim ((1 / 2 - s) / gW) / (gW * gI) * (-1))
      = 1 - gluePrim ((1 / 2 - s) / gW) / (gW * gI) := by ring
  rw [h5] at h4
  exact h4

lemma gluePhi_deriv (s : ℝ) :
    deriv gluePhi s = 1 - gluePrim ((1 / 2 - s) / gW) / (gW * gI) :=
  (hasDerivAt_gluePhi s).deriv

lemma gluePhi_deriv_fun :
    deriv gluePhi = fun s : ℝ => 1 - gluePrim ((1 / 2 - s) / gW) / (gW * gI) :=
  funext gluePhi_deriv

lemma hasDerivAt_deriv_gluePhi (s : ℝ) :
    HasDerivAt (deriv gluePhi) (16 * glueBump ((1 / 2 - s) / gW) / gI) s := by
  rw [gluePhi_deriv_fun]
  have h2 : HasDerivAt (fun u : ℝ => (1 / 2 - u) / gW) (-(1 / gW)) s := by
    have h := ((hasDerivAt_const s (1 / 2 : ℝ)).sub (hasDerivAt_id s)).div_const gW
    have h' : ((0 : ℝ) - 1) / gW = -(1 / gW) := by ring
    rw [h'] at h
    exact h
  have h3 : HasDerivAt (gluePrim ∘ fun u : ℝ => (1 / 2 - u) / gW)
      (glueBump ((1 / 2 - s) / gW) * (-(1 / gW))) s :=
    HasDerivAt.comp s (gluePrim_hasDerivAt ((1 / 2 - s) / gW)) h2
  have h3a : (gluePrim ∘ fun u : ℝ => (1 / 2 - u) / gW)
      = fun u : ℝ => gluePrim ((1 / 2 - u) / gW) := by funext x; rfl
  rw [h3a] at h3
  have h4 : HasDerivAt (fun u : ℝ => gluePrim ((1 / 2 - u) / gW) / (gW * gI))
      ((glueBump ((1 / 2 - s) / gW) * (-(1 / gW))) / (gW * gI)) s := h3.div_const _
  have h5 : HasDerivAt (fun u : ℝ => 1 - gluePrim ((1 / 2 - u) / gW) / (gW * gI))
      ((0 : ℝ) - (glueBump ((1 / 2 - s) / gW) * (-(1 / gW))) / (gW * gI)) s :=
    (hasDerivAt_const s (1 : ℝ)).sub h4
  have h6 : ((0 : ℝ) - (glueBump ((1 / 2 - s) / gW) * (-(1 / gW))) / (gW * gI))
      = 16 * glueBump ((1 / 2 - s) / gW) / gI := by
    rw [gW]; ring
  rw [h6] at h5
  exact h5

lemma gluePhi_deriv2 (s : ℝ) :
    deriv (deriv gluePhi) s = 16 * glueBump ((1 / 2 - s) / gW) / gI :=
  (hasDerivAt_deriv_gluePhi s).deriv

lemma gluePhi_cost {s : ℝ} (hs : 0 < s) :
    (deriv gluePhi s) ^ 2 + max 0 (9 / 10 - gluePhi s) * |deriv (deriv gluePhi) s| ≤ 10 := by
  have hsle : s = (2 - (1 / 2 - s) / gW) / 4 := by rw [gW]; ring
  have hψ : gluePhi s = (2 - (1 / 2 - s) / gW) / 4
      + (∫ u in (0 : ℝ)..((1 / 2 - s) / gW), gluePrim u) / gI := by
    have h1 : (2 - (1 / 2 - s) / gW) / 4 = s := hsle.symm
    rw [h1]
    rfl
  have harg : 9 / 10 - gluePhi s
      = 2 / 5 + ((1 / 2 - s) / gW) / 4
        - (∫ u in (0 : ℝ)..((1 / 2 - s) / gW), gluePrim u) / gI := by
    rw [hψ]; ring
  have ht2 : (1 / 2 - s) / gW < 2 := by rw [gW]; linarith
  have habs : |16 * glueBump ((1 / 2 - s) / gW) / gI| = 16 * glueBump ((1 / 2 - s) / gW) / gI :=
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (glueBump_nonneg _)) gI_pos.le)
  rw [gluePhi_deriv s, gluePhi_deriv2 s, harg, habs]
  exact gluePrim_cost_core ht2

end

end Work.OddVolterra.Existence
