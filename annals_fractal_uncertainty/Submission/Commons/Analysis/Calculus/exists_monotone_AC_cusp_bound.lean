import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

open MeasureTheory Set Real intervalIntegral
open scoped BigOperators

/-! ## The cusp template -/




noncomputable def templH (τ : ℝ) : ℝ :=
  if 0 < τ ∧ τ < 1 then (τ ^ (-(1/3:ℝ)) + (1-τ) ^ (-(1/3:ℝ))) / 3 else 0

noncomputable def templ (τ : ℝ) : ℝ := ∫ s in (0:ℝ)..τ, templH s

lemma templH_nonneg (τ : ℝ) : 0 ≤ templH τ := by
  rw [templH]; split_ifs with h
  · have h1 : 0 ≤ τ ^ (-(1/3:ℝ)) := Real.rpow_nonneg h.1.le _
    have h2 : 0 ≤ (1-τ) ^ (-(1/3:ℝ)) := Real.rpow_nonneg (by linarith [h.2]) _
    linarith
  · norm_num

lemma templH_eq {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    templH τ = (τ ^ (-(1/3:ℝ)) + (1-τ) ^ (-(1/3:ℝ))) / 3 := by
  rw [templH, if_pos ⟨h0,h1⟩]

lemma templH_of_nonpos {τ : ℝ} (h : τ ≤ 0) : templH τ = 0 := by
  rw [templH, if_neg]; intro hh; linarith [hh.1]

lemma templH_of_one_le {τ : ℝ} (h : 1 ≤ τ) : templH τ = 0 := by
  rw [templH, if_neg]; intro hh; linarith [hh.2]

private noncomputable def gfun (τ : ℝ) : ℝ :=
  (τ ^ (-(1/3:ℝ)) + (1-τ) ^ (-(1/3:ℝ))) / 3

private lemma gfun_eq (s : ℝ) :
    gfun s = (1/3) * (s ^ (-(1/3:ℝ)) + (1-s) ^ (-(1/3:ℝ))) := by
  simp only [gfun]; ring

private lemma int_comp_sub_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1/3:ℝ))) volume a b := by
  have hbase : IntervalIntegrable (fun u : ℝ => u ^ (-(1/3:ℝ))) volume (1-b) (1-a) :=
    intervalIntegrable_rpow' (by norm_num)
  have := hbase.comp_sub_left (1:ℝ)
  simpa using this.symm

private lemma gfun_intervalIntegrable (a b : ℝ) : IntervalIntegrable gfun volume a b := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1/3:ℝ))) volume a b :=
    intervalIntegrable_rpow' (by norm_num)
  have h2 := int_comp_sub_intervalIntegrable a b
  convert (h1.add h2).const_mul (1/3 : ℝ) using 1
  funext x; simp only [gfun]; ring

/-- On any subinterval of `(0,1]`, `templH` agrees a.e. with the closed form. -/
private lemma templH_ae_eq_gfun_of_subset {a b : ℝ} (h : uIoc a b ⊆ uIoc (0:ℝ) 1) :
    templH =ᵐ[volume.restrict (uIoc a b)] gfun := by
  show ∀ᵐ x ∂(volume.restrict (uIoc a b)), templH x = gfun x
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null _ (by simp : volume ({(1:ℝ)} : Set ℝ) = 0)
  intro x hx
  push_neg at hx
  obtain ⟨hxI, hne⟩ := hx
  have hx01 : x ∈ uIoc (0:ℝ) 1 := h hxI
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx01
  rcases lt_or_eq_of_le hx01.2 with hlt | heq
  · exact absurd (templH_eq hx01.1 hlt) hne
  · simpa using heq

private lemma templH_ae_eq_zero_of_eq_zero {a b : ℝ} (h : ∀ x ∈ uIoc a b, templH x = 0) :
    templH =ᵐ[volume.restrict (uIoc a b)] (0 : ℝ → ℝ) := by
  show ∀ᵐ x ∂(volume.restrict (uIoc a b)), templH x = (0 : ℝ → ℝ) x
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  exact Filter.Eventually.of_forall (fun x hx => h x hx)

lemma intervalIntegrable_templH_of_subset {a b : ℝ} (h : uIoc a b ⊆ uIoc (0:ℝ) 1) :
    IntervalIntegrable templH volume a b :=
  (gfun_intervalIntegrable a b).congr_ae (templH_ae_eq_gfun_of_subset h).symm

lemma intervalIntegrable_templH_of_eq_zero {a b : ℝ} (h : ∀ x ∈ uIoc a b, templH x = 0) :
    IntervalIntegrable templH volume a b :=
  IntervalIntegrable.zero.congr_ae (templH_ae_eq_zero_of_eq_zero h).symm

lemma templH_intervalIntegrable : IntervalIntegrable templH volume (0:ℝ) 1 :=
  intervalIntegrable_templH_of_subset (le_refl _)

lemma intervalIntegrable_templH (a b : ℝ) : IntervalIntegrable templH volume a b := by
  suffices H : ∀ a b : ℝ, a ≤ b → IntervalIntegrable templH volume a b by
    rcases le_total a b with h | h
    · exact H a b h
    · exact (H b a h).symm
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · exact intervalIntegrable_templH_of_eq_zero (fun x hx => by
      rw [uIoc_of_le hab] at hx; exact templH_of_nonpos (le_trans hx.2 hb))
  rcases le_or_gt 1 a with ha | ha
  · exact intervalIntegrable_templH_of_eq_zero (fun x hx => by
      rw [uIoc_of_le hab] at hx; exact templH_of_one_le (le_trans ha hx.1.le))
  have hmM : max a 0 ≤ min b 1 :=
    le_min (max_le hab hb.le) (max_le ha.le zero_le_one)
  have h_am : IntervalIntegrable templH volume a (max a 0) :=
    intervalIntegrable_templH_of_eq_zero (fun x hx => by
      rw [uIoc_of_le (le_max_left a 0)] at hx
      rcases le_or_gt a 0 with ha0 | ha0
      · rw [max_eq_right ha0] at hx
        exact templH_of_nonpos hx.2
      · rw [max_eq_left (le_of_lt ha0)] at hx
        exact absurd hx.2 (not_le.mpr hx.1))
  have h_mM : IntervalIntegrable templH volume (max a 0) (min b 1) :=
    intervalIntegrable_templH_of_subset (fun x hx => by
      rw [uIoc_of_le hmM] at hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, le_trans hx.2 (min_le_right _ _)⟩)
  have h_Mb : IntervalIntegrable templH volume (min b 1) b :=
    intervalIntegrable_templH_of_eq_zero (fun x hx => by
      rw [uIoc_of_le (min_le_left b 1)] at hx
      rcases le_or_gt b 1 with hb1 | hb1
      · rw [min_eq_left hb1] at hx
        exact absurd hx.2 (not_le.mpr hx.1)
      · rw [min_eq_right hb1.le] at hx
        exact templH_of_one_le hx.1.le)
  exact IntervalIntegrable.trans h_am (IntervalIntegrable.trans h_mM h_Mb)

lemma intervalIntegrable_templH_affine {c d : ℝ} (hd : 0 < d) (x y : ℝ) :
    IntervalIntegrable (fun u => templH ((u - c)/d)) volume x y := by
  have h1 : IntervalIntegrable (fun v : ℝ => templH (v * d⁻¹)) volume (x - c) (y - c) := by
    have hbase : IntervalIntegrable templH volume ((x - c)/d) ((y - c)/d) :=
      intervalIntegrable_templH _ _
    have h := IntervalIntegrable.comp_mul_left hbase (c := d⁻¹)
    rw [show ((x - c)/d)/(d⁻¹) = x - c by field_simp,
        show ((y - c)/d)/(d⁻¹) = y - c by field_simp] at h
    simpa [mul_comm] using h
  have h2 := IntervalIntegrable.comp_sub_right h1 c
  simpa [div_eq_mul_inv, add_sub_cancel_left, add_comm, add_left_comm, add_assoc] using h2

lemma templ_zero : templ 0 = 0 := by simp [templ]

lemma templ_of_nonpos {τ : ℝ} (h : τ ≤ 0) : templ τ = 0 := by
  rw [templ, integral_of_ge h]
  have hz : (∫ x in Ioc τ 0, templH x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun x hx => templH_of_nonpos (le_trans hx.2 (le_refl 0)))]
    simp
  rw [hz, neg_zero]

private lemma int_rpow_third : (∫ s in (0:ℝ)..1, s ^ (-(1/3:ℝ))) = 3/2 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/3))), Real.one_rpow,
    show (-(1/3:ℝ) + 1) = (2/3:ℝ) by norm_num, Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0)]
  norm_num

private lemma int_rpow_third_sub : (∫ s in (0:ℝ)..1, (1-s) ^ (-(1/3:ℝ))) = 3/2 := by
  rw [show (∫ s in (0:ℝ)..1, (1-s) ^ (-(1/3:ℝ)))
      = ∫ s in (1:ℝ)-1..(1:ℝ)-0, s ^ (-(1/3:ℝ)) from
      integral_comp_sub_left (f := fun s : ℝ => s ^ (-(1/3:ℝ))) (d := 1)]
  norm_num
  exact int_rpow_third

lemma templH_int_01 : (∫ s in (0:ℝ)..1, templH s) = 1 := by
  rw [intervalIntegral.integral_congr_ae
    (MeasureTheory.ae_imp_of_ae_restrict (templH_ae_eq_gfun_of_subset (le_refl _)))]
  show (∫ s in (0:ℝ)..1, gfun s) = 1
  have hgf : gfun = fun s => (1/3) * (s ^ (-(1/3:ℝ)) + (1-s) ^ (-(1/3:ℝ))) :=
    funext gfun_eq
  rw [hgf, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_rpow' (by norm_num))
      (int_comp_sub_intervalIntegrable 0 1), int_rpow_third, int_rpow_third_sub]
  norm_num

lemma templ_one : templ 1 = 1 := by rw [templ, templH_int_01]

lemma templ_of_one_le {τ : ℝ} (h : 1 ≤ τ) : templ τ = 1 := by
  have hi2 : IntervalIntegrable templH volume (1:ℝ) τ :=
    intervalIntegrable_templH_of_eq_zero (fun x hx => by
      rw [uIoc_of_le h] at hx; exact templH_of_one_le hx.1.le)
  have hadd := intervalIntegral.integral_add_adjacent_intervals templH_intervalIntegrable hi2
  have hz : (∫ x in (1:ℝ)..τ, templH x) = 0 := by
    have : (∫ x in (1:ℝ)..τ, templH x) = ∫ x in (1:ℝ)..τ, (0:ℝ) :=
      intervalIntegral.integral_congr (fun x hx => by
        rw [uIcc_of_le h] at hx; exact templH_of_one_le hx.1)
    rw [this]; simp
  rw [templ, ← hadd, templH_int_01, hz, add_zero]




lemma templ_nonneg (τ : ℝ) : 0 ≤ templ τ := by
  rcases le_or_gt τ 0 with h | h
  · rw [templ_of_nonpos h]
  · rw [templ, intervalIntegral.integral_of_le h.le]
    exact MeasureTheory.integral_nonneg (fun x => templH_nonneg x)

lemma templ_le_one (τ : ℝ) : templ τ ≤ 1 := by
  rcases le_or_gt τ 1 with h | h
  · rcases le_or_gt τ 0 with h' | h'
    · rw [templ_of_nonpos h']; norm_num
    · rw [← templ_one, templ, templ]
      exact integral_mono_interval le_rfl h'.le h
        (Filter.Eventually.of_forall (fun x => templH_nonneg x))
        templH_intervalIntegrable
  · rw [templ_of_one_le h.le]

lemma templ_mono : Monotone templ := by
  intro τ1 τ2 h12
  rcases le_or_gt τ2 0 with h2 | h2
  · rw [templ_of_nonpos h2, templ_of_nonpos (le_trans h12 h2)]
  rcases le_or_gt 1 τ1 with h1 | h1
  · rw [templ_of_one_le h1, templ_of_one_le (le_trans h1 h12)]
  rcases le_or_gt τ1 0 with h1' | h1'
  · rw [templ_of_nonpos h1']; exact templ_nonneg τ2
  rcases le_or_gt 1 τ2 with h2' | h2'
  · rw [templ_of_one_le h2']; exact templ_le_one τ1
  have hτ2pos : 0 < τ2 := lt_of_lt_of_le h1' h12
  have hτ2le1 : τ2 ≤ 1 := le_of_lt h2'
  rw [templ, templ]
  refine integral_mono_interval (c := 0) (d := τ2) le_rfl h1'.le h12
    (Filter.Eventually.of_forall (fun x => templH_nonneg x)) ?_
  exact intervalIntegrable_templH_of_subset (fun x hx => by
    rw [uIoc_of_le hτ2pos.le] at hx
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ⟨hx.1, le_trans hx.2 hτ2le1⟩)

private lemma int_comp_sub_intervalIntegrable_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (1-x) ^ r) volume a b := by
  have hbase : IntervalIntegrable (fun u : ℝ => u ^ r) volume (1-b) (1-a) :=
    intervalIntegrable_rpow' hr
  have := hbase.comp_sub_left (1:ℝ)
  simpa using this.symm

private lemma int_rpow_two_third : (∫ s in (0:ℝ)..1, s ^ (-(2/3:ℝ))) = 3 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(2/3))), Real.one_rpow,
    show (-(2/3:ℝ) + 1) = (1/3:ℝ) by norm_num, Real.zero_rpow (by norm_num : (1/3:ℝ) ≠ 0)]
  norm_num

private lemma int_rpow_two_third_sub : (∫ s in (0:ℝ)..1, (1-s) ^ (-(2/3:ℝ))) = 3 := by
  rw [show (∫ s in (0:ℝ)..1, (1-s) ^ (-(2/3:ℝ)))
      = ∫ s in (1:ℝ)-1..(1:ℝ)-0, s ^ (-(2/3:ℝ)) from
      integral_comp_sub_left (f := fun s : ℝ => s ^ (-(2/3:ℝ))) (d := 1)]
  norm_num
  exact int_rpow_two_third

lemma templ_lower_left {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (1/2) * τ ^ (2/3:ℝ) ≤ templ τ := by
  have hτ : (∫ s in (0:ℝ)..τ, (1/3) * s ^ (-(1/3:ℝ))) = (1/2) * τ ^ (2/3:ℝ) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ) < (-(1/3)))),
      show (-(1/3:ℝ)+1) = (2/3:ℝ) by norm_num, Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0)]
    ring
  rw [templ, ← hτ]
  refine integral_mono_on_of_le_Ioo h0 ?_ ?_ ?_
  · exact (intervalIntegrable_rpow' (by norm_num)).const_mul (1/3)
  · exact intervalIntegrable_templH_of_subset (fun x hx => by
      rw [uIoc_of_le h0] at hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨hx.1, le_trans hx.2 h1⟩)
  · intro s hs
    rw [templH_eq hs.1 (lt_of_lt_of_le hs.2 h1)]
    have : 0 ≤ (1-s) ^ (-(1/3:ℝ)) := Real.rpow_nonneg (by linarith [lt_of_lt_of_le hs.2 h1]) _
    linarith

lemma templ_lower_right {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (1/2) * (1-τ) ^ (2/3:ℝ) ≤ 1 - templ τ := by
  have h0τ : IntervalIntegrable templH volume (0:ℝ) τ := intervalIntegrable_templH_of_subset (fun x hx => by
      rw [uIoc_of_le h0] at hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨hx.1, le_trans hx.2 h1⟩)
  have hτ1 : IntervalIntegrable templH volume τ 1 := intervalIntegrable_templH_of_subset (fun x hx => by
      rw [uIoc_of_le h1] at hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨lt_of_le_of_lt h0 hx.1, hx.2⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0τ hτ1
  have hsub : 1 - templ τ = ∫ s in τ..1, templH s := by
    rw [templ]; linarith [hadd, templH_int_01]
  rw [hsub]
  have hτ : (∫ s in τ..1, (1/3) * (1-s) ^ (-(1/3:ℝ))) = (1/2) * (1-τ) ^ (2/3:ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    rw [show (∫ s in τ..1, (1-s) ^ (-(1/3:ℝ)))
        = ∫ s in (1:ℝ)-1..(1:ℝ)-τ, s ^ (-(1/3:ℝ)) from
        integral_comp_sub_left (f := fun s : ℝ => s ^ (-(1/3:ℝ))) (d := 1)]
    rw [show (1:ℝ) - 1 = 0 by norm_num,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ) < (-(1/3)))),
      show (-(1/3:ℝ)+1) = (2/3:ℝ) by norm_num, Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0)]
    ring
  rw [← hτ]
  refine integral_mono_on_of_le_Ioo h1 ?_ ?_ ?_
  · exact (int_comp_sub_intervalIntegrable_rpow (by norm_num : (-1:ℝ) < (-(1/3))) τ 1).const_mul (1/3)
  · exact hτ1
  · intro s hs
    rw [templH_eq (lt_of_le_of_lt h0 hs.1) hs.2]
    have : 0 ≤ s ^ (-(1/3:ℝ)) := Real.rpow_nonneg (by linarith [lt_of_le_of_lt h0 hs.1]) _
    linarith

private lemma templH_sq_bound {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    (templH s)^2 ≤ (2/9) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ))) := by
  rw [templH_eq h0 h1, div_pow]
  have e1 : (s ^ (-(1/3:ℝ)))^2 = s ^ (-(2/3:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  have e2 : ((1-s) ^ (-(1/3:ℝ)))^2 = (1-s) ^ (-(2/3:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  rw [show (s ^ (-(1/3:ℝ)) + (1-s) ^ (-(1/3:ℝ)))^2 / 3^2
      = (2/9) * ((s ^ (-(1/3:ℝ)))^2 / 2 + (s ^ (-(1/3:ℝ))) * ((1-s) ^ (-(1/3:ℝ))) + ((1-s) ^ (-(1/3:ℝ)))^2 / 2) by ring]
  rw [e1, e2]
  have hsq : 0 ≤ (s ^ (-(1/3:ℝ)) - (1-s) ^ (-(1/3:ℝ)))^2 := sq_nonneg _
  nlinarith [hsq]




private lemma R_nonneg {s : ℝ} (hs : s ∈ Ioc (0:ℝ) 1) :
    0 ≤ (2/9:ℝ) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ))) := by
  have h1 : 0 ≤ s ^ (-(2/3:ℝ)) := Real.rpow_nonneg hs.1.le _
  have h2 : 0 ≤ (1-s) ^ (-(2/3:ℝ)) := Real.rpow_nonneg (by linarith [hs.2]) _
  linarith

lemma templ_sq_le : (∫ s in (0:ℝ)..1, (templH s)^2) ≤ 4/3 := by
  have hRint : Integrable (fun s : ℝ => (2/9) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ))))
      (volume.restrict (Ioc (0:ℝ) 1)) := by
    have hi : IntervalIntegrable (fun s : ℝ => (2/9) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ))))
        volume (0:ℝ) 1 :=
      ((intervalIntegrable_rpow' (r := -(2/3)) (by norm_num)).add
        (int_comp_sub_intervalIntegrable_rpow (r := -(2/3)) (by norm_num) 0 1)).const_mul (2/9)
    have h := intervalIntegrable_iff.mp hi
    rwa [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
  have hle : (fun s : ℝ => (templH s)^2) ≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      (fun s : ℝ => (2/9) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ)))) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq, templH_of_one_le le_rfl]
      simpa using R_nonneg (s := (1:ℝ)) (by constructor <;> norm_num)
    · exact templH_sq_bound hs.1 hlt
  have hval : (∫ s in Ioc (0:ℝ) 1, (2/9:ℝ) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ)))) = 4/3 := by
    rw [← integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (intervalIntegrable_rpow' (r := -(2/3)) (by norm_num))
        (int_comp_sub_intervalIntegrable_rpow (r := -(2/3)) (by norm_num) 0 1),
      int_rpow_two_third, int_rpow_two_third_sub]
    norm_num
  rw [integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  calc (∫ s in Ioc (0:ℝ) 1, (templH s)^2)
      ≤ (∫ s in Ioc (0:ℝ) 1, (2/9:ℝ) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ)))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => sq_nonneg _)) hRint hle
    _ = 4/3 := hval





noncomputable def posS (A : Finset ℝ) : Finset ℝ := A.filter (fun a => 0 < a)
noncomputable def posm (A : Finset ℝ) : ℕ := (posS A).card
noncomputable def posE (A : Finset ℝ) : Fin (posm A) ↪o ℝ := (posS A).orderEmbOfFin rfl

noncomputable def cval (A : Finset ℝ) : ℝ := (100 * ((A.card : ℝ) + 1))⁻¹

noncomputable def nodeVal (A : Finset ℝ) (j : ℕ) : ℝ :=
  if h0 : j = 0 then 0 else if h : j ≤ posm A then posE A ⟨j-1, by omega⟩ else 1

@[simp] lemma nodeVal_zero (A : Finset ℝ) : nodeVal A 0 = 0 := by
  rw [nodeVal, dif_pos rfl]

lemma nodeVal_of_pos_le {A : Finset ℝ} {j : ℕ} (h0 : j ≠ 0) (hj : j ≤ posm A) :
    nodeVal A j = posE A ⟨j-1, by omega⟩ := by
  rw [nodeVal, dif_neg h0, dif_pos hj]

lemma nodeVal_of_lt {A : Finset ℝ} {j : ℕ} (hj : posm A < j) : nodeVal A j = 1 := by
  rw [nodeVal, dif_neg (by omega), dif_neg (by omega)]

lemma posE_mem (A : Finset ℝ) (i : Fin (posm A)) : posE A i ∈ posS A :=
  (posS A).orderEmbOfFin_mem (rfl : (posS A).card = posm A) i

lemma posE_pos (A : Finset ℝ) (i : Fin (posm A)) : 0 < posE A i := by
  have h := posE_mem A i
  rw [posS, Finset.mem_filter] at h
  exact h.2

lemma posE_le_half (A : Finset ℝ) (hA : ∀ a ∈ A, |a| ≤ 1/2) (i : Fin (posm A)) :
    posE A i ≤ 1/2 := by
  have h := posE_mem A i
  rw [posS, Finset.mem_filter] at h
  have := hA _ h.1
  rw [abs_le] at this
  linarith [this.2]



lemma nodeVal_eq_posE (A : Finset ℝ) (i : Fin (posm A)) :
    nodeVal A ((i:ℕ) + 1) = posE A i := by
  rw [nodeVal_of_pos_le (by omega) (by omega)]
  congr 1

lemma nodeVal_succ {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) :
    nodeVal A j < nodeVal A (j+1) := by
  rcases eq_or_ne j 0 with rfl | hj0
  · rcases eq_or_ne (posm A) 0 with hm0 | hm0
    · rw [nodeVal_zero, nodeVal_of_lt (by omega)]; norm_num
    · rw [nodeVal_zero, nodeVal_of_pos_le (by omega) (by omega)]
      exact posE_pos A ⟨0, by omega⟩
  · rw [nodeVal_of_pos_le hj0 hj]
    rcases lt_or_eq_of_le hj with hlt | heq
    · rw [nodeVal_of_pos_le (by omega) (by omega)]
      exact (posE A).strictMono (by rw [Fin.lt_def]; exact Nat.sub_one_lt hj0)
    · subst heq
      rw [nodeVal_of_lt (by omega)]
      exact lt_of_le_of_lt (posE_le_half A hA ⟨posm A - 1, by omega⟩) (by norm_num)

lemma exists_nodeVal_of_mem {A : Finset ℝ} {a : ℝ} (ha : a ∈ A) (ha0 : 0 < a) :
    ∃ k, 1 ≤ k ∧ k ≤ posm A ∧ nodeVal A k = a := by
  have hmem : a ∈ posS A := by simp [posS, ha, ha0]
  have hrange : a ∈ Set.range (posE A) := by
    rw [show Set.range (posE A) = (posS A : Set ℝ) from by
      rw [show posE A = (posS A).orderEmbOfFin (rfl : (posS A).card = posm A) from rfl]
      exact Finset.range_orderEmbOfFin _ _]
    exact hmem
  obtain ⟨i, hi⟩ := hrange
  exact ⟨(i:ℕ) + 1, by omega, by omega, by rw [nodeVal_eq_posE]; exact hi⟩


/-! ## Node values, times, and the weight function -/

noncomputable def deltaV (A : Finset ℝ) (j : ℕ) : ℝ := nodeVal A (j+1) - nodeVal A j
noncomputable def UU (A : Finset ℝ) (j : ℕ) : ℝ := (deltaV A j / (2 * cval A)) ^ (3/2:ℝ)
noncomputable def Ssum (A : Finset ℝ) : ℝ := ∑ j ∈ Finset.range (posm A + 1), UU A j
noncomputable def LL (A : Finset ℝ) (j : ℕ) : ℝ := UU A j / Ssum A
noncomputable def nodeTime (A : Finset ℝ) (j : ℕ) : ℝ := ∑ k ∈ Finset.range j, LL A k
noncomputable def wfun (A : Finset ℝ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (posm A + 1), (deltaV A j / LL A j) * templH ((u - nodeTime A j) / LL A j)
noncomputable def psi (A : Finset ℝ) : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, wfun A u

lemma cval_pos (A : Finset ℝ) : 0 < cval A := by
  rw [cval]; positivity

lemma deltaV_zero_of_lt {A : Finset ℝ} {j : ℕ} (hj : posm A < j) : deltaV A j = 0 := by
  rw [deltaV, nodeVal_of_lt hj, nodeVal_of_lt (by omega)]; ring

lemma deltaV_pos {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) :
    0 < deltaV A j := by
  rw [deltaV]; linarith [nodeVal_succ hA hj]

lemma deltaV_nonneg {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) (j : ℕ) : 0 ≤ deltaV A j := by
  rcases le_or_gt j (posm A) with h | h
  · exact le_of_lt (deltaV_pos hA h)
  · rw [deltaV_zero_of_lt h]

lemma UU_nonneg {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) (j : ℕ) : 0 ≤ UU A j := by
  rw [UU]
  exact Real.rpow_nonneg (div_nonneg (deltaV_nonneg hA j) (by linarith [cval_pos A])) _

lemma UU_pos {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) :
    0 < UU A j := by
  rw [UU]
  exact Real.rpow_pos_of_pos (div_pos (deltaV_pos hA hj) (by linarith [cval_pos A])) _

lemma sum_deltaV (A : Finset ℝ) : ∑ j ∈ Finset.range (posm A + 1), deltaV A j = 1 := by
  have h := Finset.sum_range_sub (fun j => nodeVal A j) (posm A + 1)
  simp only [deltaV] at h ⊢
  rw [h, nodeVal_zero]
  have : nodeVal A (posm A + 1) = 1 := nodeVal_of_lt (by omega)
  rw [this]; ring

lemma two_cval_mul_le_one (A : Finset ℝ) : 2 * cval A * (posm A + 1 : ℕ) ≤ 1 := by
  have hn_le : ((posm A + 1 : ℕ) : ℝ) ≤ (A.card : ℝ) + 1 := by
    have : posm A ≤ A.card := by rw [posm]; exact Finset.card_filter_le _ _
    exact_mod_cast (Nat.add_le_add_right this 1)
  have hpos : (0:ℝ) < 100 * ((A.card : ℝ) + 1) := by positivity
  have hcoef : 0 ≤ 2 * (100 * ((A.card : ℝ) + 1))⁻¹ := by positivity
  rw [cval]
  calc 2 * (100 * ((A.card : ℝ) + 1))⁻¹ * ((posm A + 1 : ℕ) : ℝ)
      ≤ 2 * (100 * ((A.card : ℝ) + 1))⁻¹ * ((A.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hn_le hcoef
    _ = 2 / 100 := by field_simp
    _ ≤ 1 := by norm_num

lemma Ssum_ge_one {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) : 1 ≤ Ssum A := by
  set n := posm A + 1 with hn
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  have hex : ∃ j ∈ Finset.range n, (1:ℝ)/(n:ℝ) ≤ deltaV A j := by
    apply Finset.exists_le_of_sum_le (s := Finset.range n) (f := fun _ : ℕ => (1:ℝ)/(n:ℝ))
        (g := fun j => deltaV A j) ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        show (n:ℝ) * (1/(n:ℝ)) = 1 by rw [mul_one_div, div_self (by positivity : (n:ℝ) ≠ 0)],
        show ∑ j ∈ Finset.range n, deltaV A j = 1 by rw [hn]; exact sum_deltaV A]
  obtain ⟨j, hj, hle⟩ := hex
  have hUU : 1 ≤ UU A j := by
    rw [UU]
    have hc : 0 < 2 * cval A := by linarith [cval_pos A]
    have hbase : (1:ℝ) ≤ deltaV A j / (2 * cval A) := by
      rw [le_div_iff₀ hc, one_mul]
      have h2 : 2 * cval A ≤ 1 / (n:ℝ) := by
        rw [le_div_iff₀ hnpos, hn]; exact two_cval_mul_le_one A
      linarith
    exact Real.one_le_rpow (x := deltaV A j / (2 * cval A)) (z := (3/2:ℝ)) hbase (by norm_num)
  have hsingle : UU A j ≤ Ssum A := by
    rw [Ssum, ← hn]
    exact Finset.single_le_sum (fun i _ => UU_nonneg hA i) hj
  linarith

lemma Ssum_pos {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) : 0 < Ssum A :=
  lt_of_lt_of_le zero_lt_one (Ssum_ge_one hA)

lemma LL_nonneg {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) (j : ℕ) : 0 ≤ LL A j := by
  rw [LL]
  exact div_nonneg (UU_nonneg hA j) (le_of_lt (Ssum_pos hA))

lemma LL_pos {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) :
    0 < LL A j := by
  rw [LL]
  exact div_pos (UU_pos hA hj) (Ssum_pos hA)

lemma cval_mul_LL_rpow_le {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) :
    cval A * (LL A j) ^ (2/3:ℝ) ≤ (1/2) * deltaV A j := by
  have hS := Ssum_ge_one hA
  have hSpos : 0 < Ssum A := Ssum_pos hA
  have hd : 0 < deltaV A j := deltaV_pos hA hj
  have hc : 0 < cval A := cval_pos A
  have hdnn : 0 ≤ deltaV A j / (2 * cval A) := div_nonneg (le_of_lt hd) (by linarith)
  have hpow : (UU A j) ^ (2/3:ℝ) = deltaV A j / (2 * cval A) := by
    rw [UU, ← Real.rpow_mul hdnn,
      show (3/2:ℝ) * (2/3) = 1 by norm_num, Real.rpow_one]
  have h1 : (1:ℝ) ≤ (Ssum A) ^ (2/3:ℝ) :=
    Real.one_le_rpow (x := Ssum A) (z := (2/3:ℝ)) hS (by norm_num)
  rw [LL, Real.div_rpow (UU_nonneg hA j) (le_of_lt hSpos) (2/3), hpow,
    show cval A * (deltaV A j / (2 * cval A) / (Ssum A) ^ (2/3:ℝ))
        = deltaV A j / (2 * (Ssum A) ^ (2/3:ℝ)) by field_simp,
    div_le_iff₀ (by positivity : (0:ℝ) < 2 * (Ssum A) ^ (2/3:ℝ))]
  nlinarith [hd, h1]

lemma nodeTime_zero (A : Finset ℝ) : nodeTime A 0 = 0 := by simp [nodeTime]

lemma nodeTime_posN (A : Finset ℝ) (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    nodeTime A (posm A + 1) = 1 := by
  rw [nodeTime]
  simp only [LL, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [show ∑ k ∈ Finset.range (posm A + 1), UU A k = Ssum A from rfl]
  exact mul_inv_cancel₀ (ne_of_gt (Ssum_pos hA))

lemma nodeTime_mono {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) : Monotone (nodeTime A) := by
  intro i j hij
  rw [nodeTime, nodeTime]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun k _ _ => LL_nonneg hA k)

lemma nodeTime_strict {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {i j : ℕ} (hij : i < j)
    (hj : j ≤ posm A + 1) : nodeTime A i < nodeTime A j := by
  have hj' : j = i + (j - i) := by omega
  have hpos : 0 < ∑ k ∈ Finset.range (j - i), LL A (i + k) := by
    apply Finset.sum_pos'
    · intro k _; exact LL_nonneg hA (i + k)
    · exact ⟨0, Finset.mem_range.mpr (by omega), by simpa using LL_pos hA (by omega : i ≤ posm A)⟩
  rw [hj']
  show ∑ k ∈ Finset.range i, LL A k < ∑ k ∈ Finset.range (i + (j - i)), LL A k
  rw [Finset.sum_range_add]
  linarith

lemma nodeTime_mem {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A + 1) :
    nodeTime A j ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · rw [← nodeTime_zero A]; exact nodeTime_mono hA (by omega)
  · rw [← nodeTime_posN A hA]; exact nodeTime_mono hA hj

noncomputable def wterm (A : Finset ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  (deltaV A j / LL A j) * templH ((u - nodeTime A j) / LL A j)

lemma wfun_eq_sum (A : Finset ℝ) (u : ℝ) :
    wfun A u = ∑ j ∈ Finset.range (posm A + 1), wterm A j u := by
  simp only [wfun, wterm]

lemma nodeTime_succ (A : Finset ℝ) (j : ℕ) : nodeTime A (j+1) = nodeTime A j + LL A j := by
  rw [nodeTime, nodeTime, Finset.sum_range_succ]

lemma wterm_eq_zero_left {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A)
    {u : ℝ} (hu : u ≤ nodeTime A j) : wterm A j u = 0 := by
  rw [wterm, templH_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (le_of_lt (LL_pos hA hj))), mul_zero]

lemma wterm_eq_zero_right {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A)
    {u : ℝ} (hu : nodeTime A (j+1) ≤ u) : wterm A j u = 0 := by
  have hL : 0 < LL A j := LL_pos hA hj
  have h1 : 1 ≤ (u - nodeTime A j)/LL A j := by
    rw [le_div_iff₀ hL, one_mul]
    have := nodeTime_succ A j
    linarith
  rw [wterm, templH_of_one_le h1, mul_zero]

lemma wterm_intervalIntegrable {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) (x y : ℝ) : IntervalIntegrable (wterm A j) volume x y := by
  have h := intervalIntegrable_templH_affine (c := nodeTime A j) (d := LL A j) (LL_pos hA hj) x y
  change IntervalIntegrable (fun u => deltaV A j / LL A j * templH ((u - nodeTime A j)/LL A j)) volume x y
  exact h.const_mul _

lemma wfun_intervalIntegrable {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) (x y : ℝ) :
    IntervalIntegrable (wfun A) volume x y := by
  have hsum : IntervalIntegrable (∑ j ∈ Finset.range (posm A + 1), wterm A j) volume x y :=
    IntervalIntegrable.sum _ (fun j hj => wterm_intervalIntegrable hA (by simpa using hj) x y)
  have hfun : wfun A = ∑ j ∈ Finset.range (posm A + 1), wterm A j := by
    funext u; rw [Finset.sum_apply, wfun_eq_sum]
  rw [hfun]; exact hsum

lemma wfun_eq_wterm_on {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A)
    {u : ℝ} (hu : u ∈ Set.Icc (nodeTime A j) (nodeTime A (j+1))) : wfun A u = wterm A j u := by
  rw [wfun_eq_sum]
  refine Finset.sum_eq_single j ?_ ?_
  · intro k hk hkj
    have hkj' : k ≤ posm A := by simpa using hk
    rcases lt_or_gt_of_ne hkj with h | h
    · rw [wterm_eq_zero_right hA hkj' (le_trans (nodeTime_mono hA (by omega)) hu.1)]
    · rw [wterm_eq_zero_left hA hkj' (le_trans hu.2 (nodeTime_mono hA (by omega)))]
  · intro hj'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj'

lemma integral_templH_comp_piece {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) :
    (∫ u in nodeTime A j..nodeTime A (j+1), templH ((u - nodeTime A j)/LL A j)) = LL A j := by
  have hL : LL A j ≠ 0 := ne_of_gt (LL_pos hA hj)
  rw [show (∫ u in nodeTime A j..nodeTime A (j+1), templH ((u - nodeTime A j)/LL A j))
      = ∫ w in nodeTime A j - nodeTime A j..nodeTime A (j+1) - nodeTime A j, templH (w / LL A j) from
      integral_comp_sub_right (f := fun w => templH (w / LL A j)) (nodeTime A j)]
  rw [sub_self, nodeTime_succ A j, add_sub_cancel_left]
  rw [integral_comp_div (f := templH) (c := LL A j) hL]
  rw [zero_div, div_self hL, templH_int_01, smul_eq_mul, mul_one]

lemma integral_wterm_piece {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) :
    (∫ u in nodeTime A j..nodeTime A (j+1), wterm A j u) = deltaV A j := by
  simp only [wterm]
  rw [intervalIntegral.integral_const_mul, integral_templH_comp_piece hA hj]
  rw [div_mul_cancel₀ _ (ne_of_gt (LL_pos hA hj))]

lemma integral_wfun_piece {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) :
    (∫ u in nodeTime A j..nodeTime A (j+1), wfun A u) = deltaV A j := by
  rw [← integral_wterm_piece hA hj]
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [uIcc_of_le (nodeTime_mono hA (Nat.le_succ j))] at hu
  exact wfun_eq_wterm_on hA hj hu

lemma integral_prefix {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    ∀ k, k ≤ posm A + 1 → (∫ u in (0:ℝ)..nodeTime A k, wfun A u) = nodeVal A k := by
  intro k
  induction k with
  | zero => intro _; rw [nodeTime_zero, intervalIntegral.integral_same, nodeVal_zero]
  | succ k ih =>
    intro hk
    have hk' : k ≤ posm A := by omega
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (wfun_intervalIntegrable hA 0 (nodeTime A k))
      (wfun_intervalIntegrable hA (nodeTime A k) (nodeTime A (k+1)))
    rw [← hadd, ih (by omega), integral_wfun_piece hA hk', deltaV]
    ring

lemma wterm_nonneg {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) (u : ℝ) :
    0 ≤ wterm A j u := by
  rw [wterm]
  exact mul_nonneg (div_nonneg (le_of_lt (deltaV_pos hA hj)) (le_of_lt (LL_pos hA hj)))
    (templH_nonneg _)

lemma wfun_nonneg {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) (u : ℝ) : 0 ≤ wfun A u := by
  rw [wfun_eq_sum]
  exact Finset.sum_nonneg (fun j hj => wterm_nonneg hA (by simpa using hj) u)

lemma wfun_of_nonpos {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {u : ℝ} (hu : u ≤ 0) :
    wfun A u = 0 := by
  rw [wfun_eq_sum]
  exact Finset.sum_eq_zero (fun j hj => by
    exact wterm_eq_zero_left hA (by simpa using hj)
      (le_trans hu (nodeTime_mem hA (le_of_lt (Finset.mem_range.mp hj))).1))

lemma wfun_of_one_le {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {u : ℝ} (hu : 1 ≤ u) :
    wfun A u = 0 := by
  rw [wfun_eq_sum]
  exact Finset.sum_eq_zero (fun j hj => by
    have hj' : j ≤ posm A := by simpa using hj
    exact wterm_eq_zero_right hA hj'
      (le_trans (nodeTime_mono hA (by omega)) (le_trans (le_of_eq (nodeTime_posN A hA)) hu)))

lemma psi_zero (A : Finset ℝ) : psi A 0 = 0 := by simp [psi]

lemma psi_of_nonpos {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {t : ℝ} (ht : t ≤ 0) :
    psi A t = 0 := by
  rw [psi, intervalIntegral.integral_of_ge ht]
  have hz : (∫ u in Ioc t 0, wfun A u) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun u hu => wfun_of_nonpos hA (le_trans hu.2 (le_refl 0)))]
    simp
  rw [hz, neg_zero]

lemma psi_of_one_le {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {t : ℝ} (ht : 1 ≤ t) :
    psi A t = 1 := by
  have h1 : (∫ u in (0:ℝ)..1, wfun A u) = 1 := by
    have h := integral_prefix hA (posm A + 1) le_rfl
    rwa [nodeTime_posN A hA, nodeVal_of_lt (by omega)] at h
  have h2 : (∫ u in (1:ℝ)..t, wfun A u) = 0 := by
    have h : (∫ u in (1:ℝ)..t, wfun A u) = ∫ u in (1:ℝ)..t, (0:ℝ) :=
      intervalIntegral.integral_congr (fun u hu => by
        rw [uIcc_of_le ht] at hu; exact wfun_of_one_le hA hu.1)
    rw [h]; simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (wfun_intervalIntegrable hA 0 1) (wfun_intervalIntegrable hA 1 t)
  rw [psi, ← hadd, h1, h2, add_zero]

lemma psi_mono {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) : Monotone (psi A) := by
  intro t1 t2 h12
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (wfun_intervalIntegrable hA 0 t1) (wfun_intervalIntegrable hA t1 t2)
  have hnn : 0 ≤ ∫ u in t1..t2, wfun A u := by
    rw [intervalIntegral.integral_of_le h12]
    exact MeasureTheory.integral_nonneg (fun u => wfun_nonneg hA u)
  rw [psi, psi, ← hadd]
  linarith

lemma psi_AC {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    AbsolutelyContinuousOnInterval (psi A) (0:ℝ) 1 := by
  have h := (wfun_intervalIntegrable hA 0 1).absolutelyContinuousOnInterval_intervalIntegral
    (c := (0:ℝ)) (by simp)
  show AbsolutelyContinuousOnInterval (fun x => ∫ v in (0:ℝ)..x, wfun A v) (0:ℝ) 1
  exact h

lemma psi_hasDerivAt_ae {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    ∀ᵐ t ∂volume, t ∈ Set.Ioc (0:ℝ) 1 → HasDerivAt (psi A) (wfun A t) t := by
  have h := (wfun_intervalIntegrable hA 0 1).ae_hasDerivAt_integral
  filter_upwards [h] with t ht htmem
  exact ht (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨htmem.1.le, htmem.2⟩)
    (0:ℝ) (by simp)

lemma rpow_add_le_add_rpow_real {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  have h := NNReal.rpow_add_le_add_rpow ⟨a, ha⟩ ⟨b, hb⟩ hp hp1
  exact_mod_cast h

lemma integral_templH_eq_sub (b c : ℝ) : (∫ x in c..b, templH x) = templ b - templ c := by
  have h := intervalIntegral.integral_interval_sub_left (intervalIntegrable_templH (0:ℝ) b)
    (intervalIntegrable_templH (0:ℝ) c)
  simpa only [templ] using h.symm

lemma integral_templH_div {c d : ℝ} (hd : 0 < d) (a b : ℝ) :
    (∫ u in a..b, templH ((u - c)/d)) = d * (templ ((b - c)/d) - templ ((a - c)/d)) := by
  rw [show (∫ u in a..b, templH ((u - c)/d))
      = ∫ w in a - c..b - c, templH (w / d) from
      integral_comp_sub_right (f := fun w => templH (w / d)) c]
  rw [integral_comp_div (f := templH) (c := d) (ne_of_gt hd), smul_eq_mul,
    integral_templH_eq_sub]

lemma psi_eq_piece {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A)
    {t : ℝ} (ht : t ∈ Set.Icc (nodeTime A j) (nodeTime A (j+1))) :
    psi A t = nodeVal A j + deltaV A j * templ ((t - nodeTime A j)/LL A j) := by
  have hprefix := integral_prefix hA j (by omega)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (wfun_intervalIntegrable hA 0 (nodeTime A j)) (wfun_intervalIntegrable hA (nodeTime A j) t)
  have hpiece : (∫ u in nodeTime A j..t, wfun A u)
      = deltaV A j * templ ((t - nodeTime A j)/LL A j) := by
    have hcongr : ∀ u ∈ Set.uIcc (nodeTime A j) t, wfun A u = wterm A j u := by
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      exact wfun_eq_wterm_on hA hj ⟨hu.1, le_trans hu.2 ht.2⟩
    rw [intervalIntegral.integral_congr hcongr]
    simp only [wterm]
    rw [intervalIntegral.integral_const_mul, integral_templH_div (LL_pos hA hj),
      sub_self, zero_div, templ_zero, sub_zero]
    have hL : (LL A j) ≠ 0 := ne_of_gt (LL_pos hA hj)
    field_simp
  rw [psi, ← hadd, hprefix, hpiece]

lemma local_cusp_right {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A)
    {t : ℝ} (ht : t ∈ Set.Icc (nodeTime A j) (nodeTime A (j+1))) :
    cval A * (t - nodeTime A j)^(2/3:ℝ) ≤ psi A t - nodeVal A j := by
  have hL := LL_pos hA hj
  have hdv := deltaV_pos hA hj
  have ht0 : 0 ≤ t - nodeTime A j := by linarith [ht.1]
  have hle : t - nodeTime A j ≤ LL A j := by
    have := nodeTime_succ A j; linarith [ht.2]
  have hτmem : (t - nodeTime A j)/LL A j ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht0 hL.le, (div_le_one hL).mpr hle⟩
  have hτ := templ_lower_left hτmem.1 hτmem.2
  have hc := cval_mul_LL_rpow_le hA hj
  have hrw : ((t - nodeTime A j)/LL A j)^(2/3:ℝ)
      = (t - nodeTime A j)^(2/3:ℝ) / (LL A j)^(2/3:ℝ) := Real.div_rpow ht0 hL.le (2/3)
  rw [psi_eq_piece hA hj ht, add_sub_cancel_left]
  have hX : 0 ≤ (t - nodeTime A j)^(2/3:ℝ) := Real.rpow_nonneg ht0 _
  have hM : 0 < (LL A j)^(2/3:ℝ) := Real.rpow_pos_of_pos hL _
  calc cval A * (t - nodeTime A j)^(2/3:ℝ)
      = (cval A * (LL A j)^(2/3:ℝ)) * ((t - nodeTime A j)^(2/3:ℝ) / (LL A j)^(2/3:ℝ)) := by
        have hMne : (LL A j)^(2/3:ℝ) ≠ 0 := ne_of_gt hM
        field_simp
    _ ≤ ((1/2) * deltaV A j) * ((t - nodeTime A j)^(2/3:ℝ) / (LL A j)^(2/3:ℝ)) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg hX hM.le)
    _ = deltaV A j * ((1/2) * ((t - nodeTime A j)/LL A j)^(2/3:ℝ)) := by
        rw [hrw]; ring
    _ ≤ deltaV A j * templ ((t - nodeTime A j)/LL A j) := mul_le_mul_of_nonneg_left hτ hdv.le

lemma local_cusp_left {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A)
    {t : ℝ} (ht : t ∈ Set.Icc (nodeTime A j) (nodeTime A (j+1))) :
    cval A * (nodeTime A (j+1) - t)^(2/3:ℝ) ≤ nodeVal A (j+1) - psi A t := by
  have hL := LL_pos hA hj
  have hdv := deltaV_pos hA hj
  have ht0 : 0 ≤ t - nodeTime A j := by linarith [ht.1]
  have hle : t - nodeTime A j ≤ LL A j := by
    have := nodeTime_succ A j; linarith [ht.2]
  have hτmem : (t - nodeTime A j)/LL A j ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht0 hL.le, (div_le_one hL).mpr hle⟩
  have hτ := templ_lower_right hτmem.1 hτmem.2
  have hc := cval_mul_LL_rpow_le hA hj
  have ht1 : 0 ≤ nodeTime A (j+1) - t := by
    have := nodeTime_succ A j; linarith [ht.2]
  have hone : 1 - (t - nodeTime A j)/LL A j = (nodeTime A (j+1) - t)/LL A j := by
    rw [nodeTime_succ A j]; field_simp; ring
  have hrw : ((nodeTime A (j+1) - t)/LL A j)^(2/3:ℝ)
      = (nodeTime A (j+1) - t)^(2/3:ℝ) / (LL A j)^(2/3:ℝ) := Real.div_rpow ht1 hL.le (2/3)
  have hsub : nodeVal A (j+1) - (nodeVal A j + deltaV A j * templ ((t - nodeTime A j)/LL A j))
      = deltaV A j * (1 - templ ((t - nodeTime A j)/LL A j)) := by
    rw [deltaV]; ring
  rw [psi_eq_piece hA hj ht, hsub]
  have hX : 0 ≤ (nodeTime A (j+1) - t)^(2/3:ℝ) := Real.rpow_nonneg ht1 _
  have hM : 0 < (LL A j)^(2/3:ℝ) := Real.rpow_pos_of_pos hL _
  calc cval A * (nodeTime A (j+1) - t)^(2/3:ℝ)
      = (cval A * (LL A j)^(2/3:ℝ)) * ((nodeTime A (j+1) - t)^(2/3:ℝ) / (LL A j)^(2/3:ℝ)) := by
        have hMne : (LL A j)^(2/3:ℝ) ≠ 0 := ne_of_gt hM
        field_simp
    _ ≤ ((1/2) * deltaV A j) * ((nodeTime A (j+1) - t)^(2/3:ℝ) / (LL A j)^(2/3:ℝ)) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg hX hM.le)
    _ = deltaV A j * ((1/2) * (1 - (t - nodeTime A j)/LL A j)^(2/3:ℝ)) := by
        rw [← hrw, ← hone]; ring
    _ ≤ deltaV A j * (1 - templ ((t - nodeTime A j)/LL A j)) :=
        mul_le_mul_of_nonneg_left hτ hdv.le

lemma cusp_right {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    ∀ j ≤ posm A + 1, ∀ t ∈ Set.Icc (nodeTime A j) 1,
      cval A * (t - nodeTime A j)^(2/3:ℝ) ≤ psi A t - nodeVal A j := by
  let P : ℕ → Prop := fun k => ∀ t ∈ Set.Icc (nodeTime A k) 1,
      cval A * (t - nodeTime A k)^(2/3:ℝ) ≤ psi A t - nodeVal A k
  have hbase : P (posm A + 1) := by
    intro t ht
    rw [nodeTime_posN A hA] at ht
    have ht1 : t = 1 := le_antisymm ht.2 ht.1
    subst ht1
    rw [nodeTime_posN A hA, nodeVal_of_lt (by omega), psi_of_one_le hA le_rfl]
    norm_num
  have hstep : ∀ k < posm A + 1, P (k+1) → P k := by
    intro k hk ih t ht
    rcases le_or_gt t (nodeTime A (k+1)) with hle | hgt
    · exact local_cusp_right hA (by omega) ⟨ht.1, hle⟩
    · have hk' : k ≤ posm A := by omega
      have hL := LL_pos hA hk'
      have hc := cval_mul_LL_rpow_le hA hk'
      have ih' := ih t ⟨le_of_lt hgt, ht.2⟩
      have htk : t - nodeTime A k = (t - nodeTime A (k+1)) + LL A k := by
        rw [nodeTime_succ A k]; ring
      have hsub : (t - nodeTime A k)^(2/3:ℝ)
          ≤ (t - nodeTime A (k+1))^(2/3:ℝ) + (LL A k)^(2/3:ℝ) := by
        rw [htk]
        exact rpow_add_le_add_rpow_real (by linarith) hL.le (by norm_num) (by norm_num)
      have h1 : cval A * (t - nodeTime A k)^(2/3:ℝ)
          ≤ cval A * (t - nodeTime A (k+1))^(2/3:ℝ) + cval A * (LL A k)^(2/3:ℝ) := by
        calc cval A * (t - nodeTime A k)^(2/3:ℝ)
            ≤ cval A * ((t - nodeTime A (k+1))^(2/3:ℝ) + (LL A k)^(2/3:ℝ)) :=
              mul_le_mul_of_nonneg_left hsub (le_of_lt (cval_pos A))
          _ = cval A * (t - nodeTime A (k+1))^(2/3:ℝ) + cval A * (LL A k)^(2/3:ℝ) := by ring
      have h4 : nodeVal A (k+1) - deltaV A k = nodeVal A k := by rw [deltaV]; ring
      calc cval A * (t - nodeTime A k)^(2/3:ℝ)
          ≤ (psi A t - nodeVal A (k+1)) + (1/2) * deltaV A k := le_trans h1 (add_le_add ih' hc)
        _ ≤ psi A t - nodeVal A k := by rw [← h4]; linarith [deltaV_nonneg hA k]
  intro j hj
  exact Nat.decreasingInduction (motive := fun k _ => P k) hstep hbase hj

lemma cusp_left {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    ∀ j ≤ posm A + 1, ∀ t ∈ Set.Icc 0 (nodeTime A j),
      cval A * (nodeTime A j - t)^(2/3:ℝ) ≤ nodeVal A j - psi A t := by
  intro j
  induction j with
  | zero =>
    intro _ t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    rw [nodeTime_zero, sub_zero, nodeVal_zero, psi_zero, sub_self,
      Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), mul_zero]
  | succ k ih =>
    intro hk t ht
    have hk' : k ≤ posm A := by omega
    rcases le_or_gt (nodeTime A k) t with hle | hlt
    · exact local_cusp_left hA hk' ⟨hle, ht.2⟩
    · have hL := LL_pos hA hk'
      have hc := cval_mul_LL_rpow_le hA hk'
      have ih' := ih (by omega) t ⟨ht.1, le_of_lt hlt⟩
      have htk : nodeTime A (k+1) - t = (nodeTime A k - t) + LL A k := by
        rw [nodeTime_succ A k]; ring
      have hsub : (nodeTime A (k+1) - t)^(2/3:ℝ)
          ≤ (nodeTime A k - t)^(2/3:ℝ) + (LL A k)^(2/3:ℝ) := by
        rw [htk]
        exact rpow_add_le_add_rpow_real (by linarith) hL.le (by norm_num) (by norm_num)
      have h1 : cval A * (nodeTime A (k+1) - t)^(2/3:ℝ)
          ≤ cval A * (nodeTime A k - t)^(2/3:ℝ) + cval A * (LL A k)^(2/3:ℝ) := by
        calc cval A * (nodeTime A (k+1) - t)^(2/3:ℝ)
            ≤ cval A * ((nodeTime A k - t)^(2/3:ℝ) + (LL A k)^(2/3:ℝ)) :=
              mul_le_mul_of_nonneg_left hsub (le_of_lt (cval_pos A))
          _ = cval A * (nodeTime A k - t)^(2/3:ℝ) + cval A * (LL A k)^(2/3:ℝ) := by ring
      have h4 : nodeVal A k + deltaV A k = nodeVal A (k+1) := by rw [deltaV]; ring
      calc cval A * (nodeTime A (k+1) - t)^(2/3:ℝ)
          ≤ (nodeVal A k - psi A t) + (1/2) * deltaV A k := le_trans h1 (add_le_add ih' hc)
        _ ≤ nodeVal A (k+1) - psi A t := by rw [← h4]; linarith [deltaV_nonneg hA k]

lemma measurable_templH : Measurable templH := by
  unfold templH
  apply Measurable.ite (measurableSet_Ioo)
  · fun_prop
  · fun_prop

lemma templH_sq_integrableOn_01 : IntegrableOn (fun s : ℝ => (templH s)^2) (Ioc (0:ℝ) 1) := by
  have hRint : Integrable (fun s : ℝ => (2/9) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ))))
      (volume.restrict (Ioc (0:ℝ) 1)) := by
    have hi : IntervalIntegrable (fun s : ℝ => (2/9) * (s ^ (-(2/3:ℝ)) + (1-s) ^ (-(2/3:ℝ))))
        volume (0:ℝ) 1 :=
      ((intervalIntegrable_rpow' (r := -(2/3)) (by norm_num)).add
        (int_comp_sub_intervalIntegrable_rpow (r := -(2/3)) (by norm_num) 0 1)).const_mul (2/9)
    have h := intervalIntegrable_iff.mp hi
    rwa [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
  refine Integrable.mono' hRint (measurable_templH.pow_const 2).aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · subst heq
    rw [templH_of_one_le le_rfl, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    have := R_nonneg (s := (1:ℝ)) (by constructor <;> norm_num)
    linarith
  · exact templH_sq_bound hs.1 hlt

lemma intervalIntegrable_templH_sq_of_subset {a b : ℝ} (h : uIoc a b ⊆ uIoc (0:ℝ) 1) :
    IntervalIntegrable (fun s => (templH s)^2) volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.mono_set templH_sq_integrableOn_01 ?_
  intro x hx
  have := h hx
  rwa [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this

lemma intervalIntegrable_templH_sq_of_eq_zero {a b : ℝ}
    (h : ∀ x ∈ uIoc a b, (templH x)^2 = 0) :
    IntervalIntegrable (fun s => (templH s)^2) volume a b := by
  refine IntervalIntegrable.zero.congr_ae ?_
  show ∀ᵐ x ∂(volume.restrict (uIoc a b)), (0:ℝ) = (templH x)^2
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  exact Filter.Eventually.of_forall (fun x hx => (h x hx).symm)

lemma intervalIntegrable_templH_sq (a b : ℝ) :
    IntervalIntegrable (fun s => (templH s)^2) volume a b := by
  suffices H : ∀ a b : ℝ, a ≤ b → IntervalIntegrable (fun s => (templH s)^2) volume a b by
    rcases le_total a b with h | h
    · exact H a b h
    · exact (H b a h).symm
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · exact intervalIntegrable_templH_sq_of_eq_zero (fun x hx => by
      rw [uIoc_of_le hab] at hx
      rw [templH_of_nonpos (le_trans hx.2 hb), zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  rcases le_or_gt 1 a with ha | ha
  · exact intervalIntegrable_templH_sq_of_eq_zero (fun x hx => by
      rw [uIoc_of_le hab] at hx
      rw [templH_of_one_le (le_trans ha hx.1.le), zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  have hmM : max a 0 ≤ min b 1 := le_min (max_le hab hb.le) (max_le ha.le zero_le_one)
  have h_am : IntervalIntegrable (fun s => (templH s)^2) volume a (max a 0) :=
    intervalIntegrable_templH_sq_of_eq_zero (fun x hx => by
      rw [uIoc_of_le (le_max_left a 0)] at hx
      rcases le_or_gt a 0 with ha0 | ha0
      · rw [max_eq_right ha0] at hx
        rw [templH_of_nonpos hx.2, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      · rw [max_eq_left (le_of_lt ha0)] at hx
        exact absurd hx.2 (not_le.mpr hx.1))
  have h_mM : IntervalIntegrable (fun s => (templH s)^2) volume (max a 0) (min b 1) :=
    intervalIntegrable_templH_sq_of_subset (fun x hx => by
      rw [uIoc_of_le hmM] at hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, le_trans hx.2 (min_le_right _ _)⟩)
  have h_Mb : IntervalIntegrable (fun s => (templH s)^2) volume (min b 1) b :=
    intervalIntegrable_templH_sq_of_eq_zero (fun x hx => by
      rw [uIoc_of_le (min_le_left b 1)] at hx
      rcases le_or_gt b 1 with hb1 | hb1
      · rw [min_eq_left hb1] at hx
        exact absurd hx.2 (not_le.mpr hx.1)
      · rw [min_eq_right hb1.le] at hx
        rw [templH_of_one_le hx.1.le, zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  exact IntervalIntegrable.trans h_am (IntervalIntegrable.trans h_mM h_Mb)

noncomputable def Tsq (x : ℝ) : ℝ := ∫ s in (0:ℝ)..x, (templH s)^2
noncomputable def Isq : ℝ := ∫ s in (0:ℝ)..1, (templH s)^2

lemma Isq_le : Isq ≤ 4/3 := templ_sq_le

lemma Tsq_of_nonpos {x : ℝ} (h : x ≤ 0) : Tsq x = 0 := by
  rw [Tsq, intervalIntegral.integral_of_ge h]
  have hz : (∫ s in Ioc x 0, (templH s)^2) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun s hs => by
      rw [templH_of_nonpos (le_trans hs.2 (le_refl 0)), zero_pow (by norm_num : (2:ℕ) ≠ 0)])]
    simp
  rw [hz, neg_zero]

lemma Tsq_of_one_le {x : ℝ} (h : 1 ≤ x) : Tsq x = Isq := by
  have hz : (∫ s in (1:ℝ)..x, (templH s)^2) = 0 := by
    have hh : (∫ s in (1:ℝ)..x, (templH s)^2) = ∫ s in (1:ℝ)..x, (0:ℝ) :=
      intervalIntegral.integral_congr (fun s hs => by
        rw [uIcc_of_le h] at hs
        rw [templH_of_one_le hs.1, zero_pow (by norm_num : (2:ℕ) ≠ 0)])
    rw [hh]; simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_templH_sq 0 1) (intervalIntegrable_templH_sq 1 x)
  rw [Tsq, Isq, ← hadd, hz, add_zero]

lemma integral_templH_sq_eq_sub (b c : ℝ) :
    (∫ x in c..b, (templH x)^2) = Tsq b - Tsq c := by
  have h := intervalIntegral.integral_interval_sub_left (intervalIntegrable_templH_sq (0:ℝ) b)
    (intervalIntegrable_templH_sq (0:ℝ) c)
  simpa only [Tsq] using h.symm

lemma integral_templH_sq_div {c d : ℝ} (hd : 0 < d) (a b : ℝ) :
    (∫ u in a..b, (templH ((u - c)/d))^2) = d * (Tsq ((b - c)/d) - Tsq ((a - c)/d)) := by
  rw [show (∫ u in a..b, (templH ((u - c)/d))^2)
      = ∫ w in a - c..b - c, (templH (w / d))^2 from
      integral_comp_sub_right (f := fun w => (templH (w / d))^2) c]
  rw [integral_comp_div (f := fun w => (templH w)^2) (c := d) (ne_of_gt hd), smul_eq_mul,
    integral_templH_sq_eq_sub]

lemma intervalIntegrable_templH_sq_affine {c d : ℝ} (hd : 0 < d) (x y : ℝ) :
    IntervalIntegrable (fun u => (templH ((u - c)/d))^2) volume x y := by
  have h1 : IntervalIntegrable (fun v : ℝ => (templH (v * d⁻¹))^2) volume (x - c) (y - c) := by
    have hbase : IntervalIntegrable (fun s => (templH s)^2) volume ((x - c)/d) ((y - c)/d) :=
      intervalIntegrable_templH_sq _ _
    have h := IntervalIntegrable.comp_mul_left hbase (c := d⁻¹)
    rw [show ((x - c)/d)/(d⁻¹) = x - c by field_simp,
        show ((y - c)/d)/(d⁻¹) = y - c by field_simp] at h
    simpa [mul_comm] using h
  have h2 := IntervalIntegrable.comp_sub_right h1 c
  simpa [div_eq_mul_inv, add_sub_cancel_left, add_comm, add_left_comm, add_assoc] using h2

lemma wterm_sq_intervalIntegrable {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) (x y : ℝ) :
    IntervalIntegrable (fun u => (wterm A j u)^2) volume x y := by
  have h := intervalIntegrable_templH_sq_affine (c := nodeTime A j) (d := LL A j) (LL_pos hA hj) x y
  change IntervalIntegrable (fun u => ((deltaV A j / LL A j) * templH ((u - nodeTime A j)/LL A j))^2) volume x y
  convert h.const_mul ((deltaV A j / LL A j)^2) using 1
  ext u; rw [mul_pow]

lemma integral_wterm_sq {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) :
    (∫ u in (0:ℝ)..1, (wterm A j u)^2) = (deltaV A j)^2 / LL A j * Isq := by
  have hL := LL_pos hA hj
  have hkey : (∫ u in (0:ℝ)..1, (templH ((u - nodeTime A j)/LL A j))^2) = LL A j * Isq := by
    rw [integral_templH_sq_div hL 0 1]
    have h1 : Tsq ((1 - nodeTime A j)/LL A j) = Isq := by
      apply Tsq_of_one_le
      rw [le_div_iff₀ hL, one_mul]
      have hs := nodeTime_succ A j
      have hmem : nodeTime A (j+1) ≤ 1 := (nodeTime_mem hA (j := j+1) (by omega)).2
      linarith
    have h2 : Tsq ((0 - nodeTime A j)/LL A j) = 0 := by
      apply Tsq_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg
      · have hnn : 0 ≤ nodeTime A j := (nodeTime_mem hA (j := j) (by omega)).1
        linarith
      · exact hL.le
    rw [h1, h2, sub_zero]
  have hpt : ∀ u, (wterm A j u)^2
      = (deltaV A j / LL A j)^2 * (templH ((u - nodeTime A j)/LL A j))^2 := fun u => by
    rw [wterm, mul_pow]
  rw [show (∫ u in (0:ℝ)..1, (wterm A j u)^2)
      = ∫ u in (0:ℝ)..1, (deltaV A j / LL A j)^2 * (templH ((u - nodeTime A j)/LL A j))^2 from
      intervalIntegral.integral_congr (fun u _ => hpt u)]
  rw [intervalIntegral.integral_const_mul, hkey]
  have hLne : LL A j ≠ 0 := ne_of_gt hL
  rw [div_pow]
  field_simp

lemma wterm_mul_eq_zero {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j k : ℕ}
    (hj : j ≤ posm A) (hk : k ≤ posm A) (hjk : j ≠ k) (u : ℝ) :
    wterm A j u * wterm A k u = 0 := by
  rcases lt_or_gt_of_ne hjk with h | h
  · rcases le_or_gt u (nodeTime A k) with hu | hu
    · have hz : wterm A k u = 0 := wterm_eq_zero_left hA hk hu
      rw [hz, mul_zero]
    · have hz : wterm A j u = 0 := wterm_eq_zero_right hA hj (le_trans (nodeTime_mono hA (by omega)) hu.le)
      rw [hz, zero_mul]
  · rcases le_or_gt u (nodeTime A j) with hu | hu
    · have hz : wterm A j u = 0 := wterm_eq_zero_left hA hj hu
      rw [hz, zero_mul]
    · have hz : wterm A k u = 0 := wterm_eq_zero_right hA hk (le_trans (nodeTime_mono hA (by omega)) hu.le)
      rw [hz, mul_zero]

lemma wfun_sq_eq_sum {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) (u : ℝ) :
    (wfun A u)^2 = ∑ j ∈ Finset.range (posm A+1), (wterm A j u)^2 := by
  rw [wfun_eq_sum, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_eq_single i
    (fun k hk hki => wterm_mul_eq_zero hA (by simpa using hi) (by simpa using hk) hki.symm u)
    (fun hi' => absurd hi hi'), sq]

lemma wfun_sq_intervalIntegrable {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    IntervalIntegrable (fun u => (wfun A u)^2) volume (0:ℝ) 1 := by
  have hfun : (fun u => (wfun A u)^2)
      = ∑ j ∈ Finset.range (posm A+1), (fun u => (wterm A j u)^2) := by
    funext u; rw [Finset.sum_apply]; exact wfun_sq_eq_sum hA u
  rw [hfun]
  exact IntervalIntegrable.sum _ (fun j hj => wterm_sq_intervalIntegrable hA (by simpa using hj) 0 1)

lemma integral_wfun_sq {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    (∫ u in (0:ℝ)..1, (wfun A u)^2)
      = (∑ j ∈ Finset.range (posm A+1), (deltaV A j)^2 / LL A j) * Isq := by
  have hfun : (fun u => (wfun A u)^2)
      = fun u => ∑ j ∈ Finset.range (posm A+1), (wterm A j u)^2 :=
    funext (fun u => wfun_sq_eq_sum hA u)
  rw [hfun, intervalIntegral.integral_finset_sum
    (fun j hj => wterm_sq_intervalIntegrable hA (by simpa using hj) 0 1)]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j hj => integral_wterm_sq hA (by simpa using hj))

lemma nodeVal_mem {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A + 1) :
    nodeVal A j ∈ Set.Icc (0:ℝ) 1 := by
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [nodeVal_zero]; norm_num
  rcases le_or_gt j (posm A) with h | h
  · rw [nodeVal_of_pos_le hj0 h]
    exact ⟨le_of_lt (posE_pos A ⟨j-1, by omega⟩), le_trans (posE_le_half A hA ⟨j-1, by omega⟩) (by norm_num)⟩
  · rw [nodeVal_of_lt h]; norm_num

lemma deltaV_le_one {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ} (hj : j ≤ posm A) :
    deltaV A j ≤ 1 := by
  rw [deltaV]
  have h1 : nodeVal A (j+1) ≤ 1 := (nodeVal_mem hA (j := j+1) (by omega)).2
  have h2 : 0 ≤ nodeVal A j := (nodeVal_mem hA (j := j) (by omega)).1
  linarith

lemma rpow_three_halves_le_self {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) : (deltaV A j)^(3/2:ℝ) ≤ deltaV A j := by
  calc (deltaV A j)^(3/2:ℝ) ≤ (deltaV A j)^(1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (x := deltaV A j) (y := 3/2) (z := 1)
          (deltaV_pos hA hj) (deltaV_le_one hA hj) (by norm_num)
    _ = deltaV A j := Real.rpow_one _

lemma two_cval_rpow_mul_UU {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) :
    (2 * cval A)^(3/2:ℝ) * UU A j = (deltaV A j)^(3/2:ℝ) := by
  have hc : 0 < 2 * cval A := by linarith [cval_pos A]
  have hd : 0 ≤ deltaV A j := le_of_lt (deltaV_pos hA hj)
  have hdn : 0 ≤ deltaV A j / (2 * cval A) := div_nonneg hd hc.le
  rw [UU, ← Real.mul_rpow hc.le hdn]
  have hcne : cval A ≠ 0 := ne_of_gt (cval_pos A)
  rw [show 2 * cval A * (deltaV A j / (2 * cval A)) = deltaV A j by
    field_simp]

lemma two_cval_rpow_mul_Ssum_le_one {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    (2 * cval A)^(3/2:ℝ) * Ssum A ≤ 1 := by
  rw [Ssum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j hj => two_cval_rpow_mul_UU hA (by simpa using hj))]
  calc ∑ j ∈ Finset.range (posm A+1), (deltaV A j)^(3/2:ℝ)
      ≤ ∑ j ∈ Finset.range (posm A+1), deltaV A j :=
        Finset.sum_le_sum (fun j hj => rpow_three_halves_le_self hA (by simpa using hj))
    _ = 1 := sum_deltaV A

lemma LL_ge_deltaV_rpow {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) : (deltaV A j)^(3/2:ℝ) ≤ LL A j := by
  have hL := LL_pos hA hj
  have hS := two_cval_rpow_mul_Ssum_le_one hA
  have hSpos := Ssum_pos hA
  have hkey : ((2 * cval A)^(3/2:ℝ) * Ssum A) * LL A j = (deltaV A j)^(3/2:ℝ) := by
    rw [LL]
    rw [show ((2 * cval A)^(3/2:ℝ) * Ssum A) * (UU A j / Ssum A)
        = (2 * cval A)^(3/2:ℝ) * UU A j by field_simp]
    exact two_cval_rpow_mul_UU hA hj
  calc (deltaV A j)^(3/2:ℝ) = ((2 * cval A)^(3/2:ℝ) * Ssum A) * LL A j := hkey.symm
    _ ≤ 1 * LL A j := mul_le_mul_of_nonneg_right hS (le_of_lt hL)
    _ = LL A j := one_mul _

lemma deltaV_sq_div_LL_le_one {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) {j : ℕ}
    (hj : j ≤ posm A) : (deltaV A j)^2 / LL A j ≤ 1 := by
  have hL := LL_pos hA hj
  rw [div_le_one hL]
  calc (deltaV A j)^2 ≤ (deltaV A j)^(3/2:ℝ) := by
        rw [← Real.rpow_natCast (deltaV A j) 2]
        exact Real.rpow_le_rpow_of_exponent_ge (deltaV_pos hA hj) (deltaV_le_one hA hj) (by norm_num)
    _ ≤ LL A j := LL_ge_deltaV_rpow hA hj

lemma sum_deltaV_sq_div_le {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    ∑ j ∈ Finset.range (posm A+1), (deltaV A j)^2 / LL A j ≤ ((posm A + 1 : ℕ) : ℝ) := by
  calc ∑ j ∈ Finset.range (posm A+1), (deltaV A j)^2 / LL A j
      ≤ ∑ j ∈ Finset.range (posm A+1), (1:ℝ) :=
        Finset.sum_le_sum (fun j hj => deltaV_sq_div_LL_le_one hA (by simpa using hj))
    _ = ((posm A + 1 : ℕ) : ℝ) := by simp

lemma psi_deriv_ae {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    ∀ᵐ t ∂volume, t ∈ Set.Ioc (0:ℝ) 1 → deriv (psi A) t = wfun A t := by
  filter_upwards [psi_hasDerivAt_ae hA] with t ht htmem
  exact (ht htmem).deriv

lemma wfun_sq_integrableOn {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    Integrable (fun t => (wfun A t)^2) (volume.restrict (Ioc (0:ℝ) 1)) := by
  have h := (wfun_sq_intervalIntegrable hA).def'
  rwa [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h

lemma lintegral_deriv_bound {A : Finset ℝ} (hA : ∀ a ∈ A, |a| ≤ 1/2) :
    (∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((deriv (psi A) t)^2))
      ≤ ENNReal.ofReal (100 * ((A.card : ℝ) + 1)) := by
  have hae := psi_deriv_ae hA
  have hcongr : (∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((deriv (psi A) t)^2))
      = ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((wfun A t)^2) := by
    apply lintegral_congr_ae
    show ∀ᵐ a ∂(volume.restrict (Ioc (0:ℝ) 1)),
      ENNReal.ofReal ((deriv (psi A) a)^2) = ENNReal.ofReal ((wfun A a)^2)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hae] with t ht htmem
    rw [ht htmem]
  rw [hcongr]
  have hint := wfun_sq_integrableOn hA
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun t => (wfun A t)^2) :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  apply ENNReal.ofReal_le_ofReal
  have hbound : (∫ t in Ioc (0:ℝ) 1, (wfun A t)^2) ≤ 100 * ((A.card : ℝ) + 1) := by
    rw [← integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [integral_wfun_sq hA]
    have h1 : (∑ j ∈ Finset.range (posm A+1), (deltaV A j)^2 / LL A j) ≤ ((posm A + 1 : ℕ) : ℝ) :=
      sum_deltaV_sq_div_le hA
    have h2 : Isq ≤ 4/3 := Isq_le
    have h3 : (0:ℝ) ≤ (∑ j ∈ Finset.range (posm A+1), (deltaV A j)^2 / LL A j) := by
      apply Finset.sum_nonneg; intro j hj
      exact div_nonneg (sq_nonneg _) (le_of_lt (LL_pos hA (by simpa using hj)))
    have h4 : (posm A + 1 : ℕ) ≤ (A.card : ℝ) + 1 := by
      have : posm A ≤ A.card := by rw [posm]; exact Finset.card_filter_le _ _
      exact_mod_cast (Nat.add_le_add_right this 1)
    have h5 : (0:ℝ) ≤ Isq := by
      rw [Isq, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact MeasureTheory.integral_nonneg (fun s => sq_nonneg _)
    calc (∑ j ∈ Finset.range (posm A+1), (deltaV A j)^2 / LL A j) * Isq
        ≤ ((posm A + 1 : ℕ) : ℝ) * (4/3) := by
          apply mul_le_mul h1 h2 h5 (by positivity)
      _ ≤ 100 * ((A.card : ℝ) + 1) := by
          nlinarith [h4, show (0:ℝ) ≤ (A.card : ℝ) + 1 by positivity]
  exact hbound

theorem exists_monotone_AC_cusp_bound (A : Finset ℝ) (hA : ∀ a ∈ A, |a| ≤ 1 / 2) :
    ∃ ψ : ℝ → ℝ,
      ψ 0 = 0 ∧ ψ 1 = 1 ∧ Monotone ψ ∧
      (∀ t, t ≤ 0 → ψ t = 0) ∧ (∀ t, 1 ≤ t → ψ t = 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ t ∧ ψ t ≤ 1) ∧
      AbsolutelyContinuousOnInterval ψ 0 1 ∧
      (∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((deriv ψ t) ^ 2))
        ≤ ENNReal.ofReal (100 * ((A.card : ℝ) + 1)) ∧
      ∀ a ∈ A, ∃ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (100 * ((A.card : ℝ) + 1))⁻¹ * |t - s| ^ (2 / 3 : ℝ) ≤ |ψ t - a| := by
  refine ⟨psi A, psi_zero A, psi_of_one_le hA le_rfl, psi_mono hA, ?_, ?_, ?_,
    psi_AC hA, lintegral_deriv_bound hA, ?_⟩
  · intro t ht; exact psi_of_nonpos hA ht
  · intro t ht; exact psi_of_one_le hA ht
  · intro t ht
    exact ⟨by simpa [psi_zero] using psi_mono hA ht.1,
      by simpa [psi_of_one_le hA le_rfl] using psi_mono hA ht.2⟩
  · intro a ha
    rcases le_or_gt a 0 with ha0 | ha0
    · refine ⟨0, ⟨le_refl 0, by norm_num⟩, fun t ht => ?_⟩
      have hpsi0 : 0 ≤ psi A t := by
        have := psi_mono hA ht.1; rw [psi_zero] at this; exact this
      have hcr := cusp_right hA 0 (by omega) t (by rw [nodeTime_zero]; exact ⟨ht.1, ht.2⟩)
      rw [nodeTime_zero, nodeVal_zero, sub_zero, sub_zero] at hcr
      rw [sub_zero, abs_of_nonneg ht.1,
        abs_of_nonneg (show (0:ℝ) ≤ psi A t - a by linarith)]
      simp only [cval] at hcr ⊢
      linarith
    · obtain ⟨j, hj1, hjle, hjnv⟩ := exists_nodeVal_of_mem ha ha0
      rw [← hjnv]
      refine ⟨nodeTime A j, nodeTime_mem hA (by omega), fun t ht => ?_⟩
      have hpsij : psi A (nodeTime A j) = nodeVal A j := integral_prefix hA j (by omega)
      rcases le_or_gt (nodeTime A j) t with htge | htlt
      · have hcr := cusp_right hA j (by omega) t ⟨htge, ht.2⟩
        rw [abs_of_nonneg (show (0:ℝ) ≤ t - nodeTime A j by linarith),
          abs_of_nonneg (show (0:ℝ) ≤ psi A t - nodeVal A j by
            have := psi_mono hA htge; rw [hpsij] at this; linarith)]
        simp only [cval] at hcr ⊢
        exact hcr
      · have hcl := cusp_left hA j (by omega) t ⟨ht.1, le_of_lt htlt⟩
        rw [abs_of_nonpos (show t - nodeTime A j ≤ 0 by linarith), neg_sub,
          abs_of_nonpos (show psi A t - nodeVal A j ≤ 0 by
            have := psi_mono hA (le_of_lt htlt); rw [hpsij] at this; linarith), neg_sub]
        simp only [cval] at hcl ⊢
        exact hcl


end Commons.Analysis.Calculus