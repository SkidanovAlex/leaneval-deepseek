import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace
import Submission.Work.RefuteDrop.trN1_sign
import Submission.Work.RefuteDrop.psiA1_evals
import Submission.Work.RefuteDrop.psiA1_gAnti
import Submission.Work.RefuteDrop.psiA1_hMono

/-!
# The shape of the `y`-window function `psiA1` of the `RefuteDrop` configuration

This file determines the zero set and the sign of `psiA1 u = 3 |trN1 u| - yclip (2c - trS u)`
on `[0, 2 * π]`, and identifies the four parameters `yA1 < yA2 < yA3 < yA4` at which the `A`
branch of the trace meets the `y`-faces of the box.
-/

open Work.BoxShrink.PinchOff.RefuteDrop

namespace Work.RefuteDrop

/-! ## Elementary algebra and bounds -/

lemma trN1_eq (u : ℝ) : trN1 u = (7761/10000 : ℝ) * Real.cos u + (4907/5000 : ℝ) * Real.sin u := by
  simp only [trN1, trB1, trA]; ring

lemma trN1_add_pi (u : ℝ) : trN1 (u + Real.pi) = - trN1 u := by
  rw [trN1_eq, trN1_eq]; rw [Real.cos_add_pi, Real.sin_add_pi]; ring

lemma trA_add_pi (u : ℝ) : trA (u + Real.pi) = - trA u := by
  simp only [trA]; rw [Real.cos_add_pi, Real.sin_add_pi]; ring

lemma trS_add_pi (u : ℝ) : trS (u + Real.pi) = trS u := by
  simp only [trS]; rw [trA_add_pi]; congr 1; ring

lemma psiA1_period (u : ℝ) : psiA1 (u + Real.pi) = psiA1 u := by
  simp only [psiA1]; rw [trN1_add_pi, abs_neg, trS_add_pi]

lemma psiA1_sub_pi (u : ℝ) : psiA1 u = psiA1 (u - Real.pi) := by
  have := psiA1_period (u - Real.pi)
  rwa [sub_add_cancel] at this

lemma rpow_third_le : (2:ℝ)^(1/3:ℝ) ≤ 126/100 := by
  have hx : (0:ℝ) ≤ (2:ℝ)^(1/3:ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3 : ((2:ℝ)^(1/3:ℝ))^((3:ℕ):ℝ) ≤ ((126/100:ℝ))^((3:ℕ):ℝ) := by
    rw [Real.rpow_natCast]
    have h2 : ((2:ℝ)^(1/3:ℝ))^(3:ℕ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [h2]; norm_num
  exact (Real.rpow_le_rpow_iff hx (by norm_num) (by norm_num : (0:ℝ) < 3)).mp h3

lemma yclip_le : yclip ≤ 177/100 := by
  rw [yclip]; have := rpow_third_le; nlinarith

lemma yclip_pos : 0 < yclip := by linarith [yclip_lower]

lemma trS_ge (u : ℝ) : (682/1000:ℝ) ≤ trS u := by
  rw [trS, Real.le_sqrt (by norm_num) (le_of_lt (trS_arg_pos u))]
  nlinarith [trA_sq_le u]

lemma trN1_lower_left (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (ang (7/10))) : (3/4 : ℝ) ≤ trN1 u := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, trN1_eq, Real.cos_zero, Real.sin_zero]; norm_num
  have hu2pos : (0:ℝ) < u/2 := by linarith
  have hu2lt : u/2 < Real.pi/2 := by
    have h := ang_lt_pi (by norm_num : (0:ℝ) < 7/10)
    linarith [hu.2]
  set t : ℝ := Real.tan (u/2) with ht
  have har : Real.arctan t = u/2 := by
    rw [ht]; exact Real.arctan_tan (by linarith) hu2lt
  have hmem1 : u/2 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) := ⟨by linarith, hu2lt⟩
  have hmem2 : Real.arctan (7/10) ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) := Real.arctan_mem_Ioo _
  have ht_le : t ≤ 7/10 := by
    have h := (Real.strictMonoOn_tan.le_iff_le hmem1 hmem2).mpr (by
      have h2 : u ≤ ang (7/10) := hu.2
      simp only [ang] at h2; linarith)
    rwa [Real.tan_arctan] at h
  have ht_nonneg : 0 ≤ t := by
    rw [ht]; exact le_of_lt (Real.tan_pos_of_pos_of_lt_pi_div_two hu2pos hu2lt)
  have hu_eq : u = ang t := by rw [ang]; linarith [har]
  rw [hu_eq, trN1_eq, cos_ang, sin_ang]
  have hval : (7761/10000 : ℝ) * ((1-t^2)/(1+t^2)) + (4907/5000)*(2*t/(1+t^2))
      = ((7761/10000)*(1-t^2) + (4907/5000)*(2*t))/(1+t^2) := by field_simp
  rw [hval, le_div_iff₀ (by positivity : (0:ℝ) < 1 + t^2)]
  have hcoef : 0 ≤ 2*(4907/5000:ℝ) - (7761/10000 + 3/4) * t := by nlinarith [ht_le]
  have hprod : 0 ≤ t * (2*(4907/5000:ℝ) - (7761/10000 + 3/4) * t) := mul_nonneg ht_nonneg hcoef
  nlinarith [hprod]

/-! ## The two signed versions of `psiA1` -/

noncomputable def gA1 (u : ℝ) : ℝ := 3 * trN1 u - yclip * (2 * (97/100) - trS u)
noncomputable def hA1 (u : ℝ) : ℝ := -3 * trN1 u - yclip * (2 * (97/100) - trS u)

lemma gA1_eq_psiA1 (u : ℝ) (h : 0 ≤ trN1 u) : gA1 u = psiA1 u := by
  simp only [gA1, psiA1, abs_of_nonneg h]

lemma hA1_eq_psiA1 (u : ℝ) (h : trN1 u ≤ 0) : hA1 u = psiA1 u := by
  rw [hA1, psiA1, abs_of_nonpos h]; ring

lemma continuous_trN1 : Continuous trN1 := by
  rw [show trN1 = fun u : ℝ => (7761/10000:ℝ) * Real.cos u + (4907/5000:ℝ) * Real.sin u
    from funext trN1_eq]
  fun_prop

lemma continuous_clip : Continuous (fun u : ℝ => yclip * (2 * (97/100) - trS u)) :=
  continuous_const.mul (continuous_const.sub continuous_trS)

lemma continuous_gA1 : Continuous gA1 := by
  rw [show gA1 = fun u => 3 * trN1 u - yclip * (2 * (97/100) - trS u) from rfl]
  exact (continuous_trN1.const_mul 3).sub continuous_clip

lemma continuous_hA1 : Continuous hA1 := by
  rw [show hA1 = fun u => -3 * trN1 u - yclip * (2 * (97/100) - trS u) from rfl]
  exact (continuous_trN1.const_mul (-3)).sub continuous_clip

lemma continuous_psiA1 : Continuous psiA1 := by
  rw [show psiA1 = fun u => 3 * |trN1 u| - yclip * (2 * (97/100) - trS u) from rfl]
  exact ((continuous_trN1.abs).const_mul 3).sub continuous_clip

lemma gA1_anti : StrictAntiOn gA1 (Set.Icc (ang (7/10)) (ang (9/2))) := by
  rw [show gA1 = fun u => 3 * trN1 u - yclip * (2 * (97/100) - trS u) from rfl]
  exact psiA1_gAnti

lemma hA1_mono : StrictMonoOn hA1 (Set.Icc (ang (5/2)) Real.pi) := by
  rw [show hA1 = fun u => -3 * trN1 u - yclip * (2 * (97/100) - trS u) from rfl]
  exact psiA1_hMono

/-! ## The general `sInf` lemma -/

lemma sInf_zeroSet_pos_neg (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hle : a ≤ b)
    (ha : 0 < f a) (hb : f b < 0) :
    sInf {u : ℝ | u ∈ Set.Icc a b ∧ f u = 0} ∈ Set.Ioo a b ∧
      f (sInf {u : ℝ | u ∈ Set.Icc a b ∧ f u = 0}) = 0 := by
  set S := {u : ℝ | u ∈ Set.Icc a b ∧ f u = 0} with hS
  have hclosed : IsClosed S := by
    rw [hS]; exact isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hnonempty : S.Nonempty := by
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hle hf.continuousOn
      (show (0:ℝ) ∈ Set.Icc (f b) (f a) from ⟨le_of_lt hb, le_of_lt ha⟩)
    exact ⟨c, hc, hfc⟩
  have hmem : sInf S ∈ S := hclosed.csInf_mem hnonempty ⟨a, fun x hx => hx.1.1⟩
  refine ⟨⟨?_, ?_⟩, hmem.2⟩
  · refine lt_of_le_of_ne hmem.1.1 (Ne.symm ?_)
    intro h; rw [h] at hmem; linarith [hmem.2, ha]
  · refine lt_of_le_of_ne hmem.1.2 ?_
    intro h; rw [h] at hmem; linarith [hmem.2, hb]

lemma sInf_zeroSet_neg_pos (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hle : a ≤ b)
    (ha : f a < 0) (hb : 0 < f b) :
    sInf {u : ℝ | u ∈ Set.Icc a b ∧ f u = 0} ∈ Set.Ioo a b ∧
      f (sInf {u : ℝ | u ∈ Set.Icc a b ∧ f u = 0}) = 0 := by
  set S := {u : ℝ | u ∈ Set.Icc a b ∧ f u = 0} with hS
  have hclosed : IsClosed S := by
    rw [hS]; exact isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hnonempty : S.Nonempty := by
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hle hf.continuousOn
      (show (0:ℝ) ∈ Set.Icc (f a) (f b) from ⟨le_of_lt ha, le_of_lt hb⟩)
    exact ⟨c, hc, hfc⟩
  have hmem : sInf S ∈ S := hclosed.csInf_mem hnonempty ⟨a, fun x hx => hx.1.1⟩
  refine ⟨⟨?_, ?_⟩, hmem.2⟩
  · refine lt_of_le_of_ne hmem.1.1 (Ne.symm ?_)
    intro h; rw [h] at hmem; linarith [hmem.2, ha]
  · refine lt_of_le_of_ne hmem.1.2 ?_
    intro h; rw [h] at hmem; linarith [hmem.2, hb]


/-! ## The four points -/

private lemma ang_lt_ang' : ang (7/10) < ang (5/2) := ang_lt_ang (by norm_num)
private lemma ang_lt_ang'' : ang (5/2) < ang (9/2) := ang_lt_ang (by norm_num)
private lemma ang_lt_ang5 : ang (9/2) < ang 5 := ang_lt_ang (by norm_num)
private lemma ang_lt_ang14 : ang 5 < ang 14 := ang_lt_ang (by norm_num)
private lemma ang14_lt_pi : ang 14 < Real.pi := ang_lt_pi (by norm_num)
private lemma ang92_lt_pi : ang (9/2) < Real.pi := lt_trans ang_lt_ang5 (lt_trans ang_lt_ang14 ang14_lt_pi)
private lemma ang7_pos : 0 < ang (7/10) := ang_pos (by norm_num)

lemma gA1_ang7 : 0 < gA1 (ang (7/10)) := by simpa only [gA1] using psiA1_evals.1
lemma gA1_ang52 : gA1 (ang (5/2)) < 0 := by simpa only [gA1] using psiA1_evals.2.1
lemma hA1_ang5 : hA1 (ang 5) < 0 := by simpa only [hA1] using psiA1_evals.2.2.1
lemma hA1_ang14 : 0 < hA1 (ang 14) := by simpa only [hA1] using psiA1_evals.2.2.2

lemma hA1_ang92 : hA1 (ang (9/2)) < 0 := by
  have h1 : ang (9/2) ∈ Set.Icc (ang (5/2)) Real.pi := ⟨ang_lt_ang''.le, ang92_lt_pi.le⟩
  have h2 : ang 5 ∈ Set.Icc (ang (5/2)) Real.pi := ⟨le_trans ang_lt_ang''.le ang_lt_ang5.le, le_trans ang_lt_ang14.le ang14_lt_pi.le⟩
  have := (hA1_mono.lt_iff_lt h1 h2).mpr ang_lt_ang5
  linarith [this, hA1_ang5]

lemma yA1_mem : yA1 ∈ Set.Ioo (ang (7/10)) (ang (5/2)) ∧ psiA1 yA1 = 0 := by
  have hset : {u : ℝ | u ∈ Set.Icc (ang (7/10)) (ang (5/2)) ∧ psiA1 u = 0}
      = {u : ℝ | u ∈ Set.Icc (ang (7/10)) (ang (5/2)) ∧ gA1 u = 0} := by
    ext u; constructor
    · rintro ⟨hu, h0⟩
      have hN : 0 < trN1 u := trN1_sign.1 u ⟨le_trans ang7_pos.le hu.1, hu.2⟩
      exact ⟨hu, by rw [gA1_eq_psiA1 u hN.le, h0]⟩
    · rintro ⟨hu, h0⟩
      have hN : 0 < trN1 u := trN1_sign.1 u ⟨le_trans ang7_pos.le hu.1, hu.2⟩
      exact ⟨hu, by rw [← gA1_eq_psiA1 u hN.le, h0]⟩
  obtain ⟨hmem, hzero⟩ := sInf_zeroSet_pos_neg gA1 continuous_gA1 ang_lt_ang'.le gA1_ang7 gA1_ang52
  have hdef : yA1 = sInf {u : ℝ | u ∈ Set.Icc (ang (7/10)) (ang (5/2)) ∧ gA1 u = 0} := by
    unfold yA1; rw [hset]
  rw [hdef]
  refine ⟨hmem, ?_⟩
  have hN : 0 < trN1 (sInf {u : ℝ | u ∈ Set.Icc (ang (7/10)) (ang (5/2)) ∧ gA1 u = 0}) :=
    trN1_sign.1 _ ⟨le_trans ang7_pos.le hmem.1.le, hmem.2.le⟩
  rw [← gA1_eq_psiA1 _ hN.le]; exact hzero

lemma yA2_mem : yA2 ∈ Set.Ioo (ang (9/2)) (ang 14) ∧ psiA1 yA2 = 0 := by
  have hset : {u : ℝ | u ∈ Set.Icc (ang (9/2)) (ang 14) ∧ psiA1 u = 0}
      = {u : ℝ | u ∈ Set.Icc (ang (9/2)) (ang 14) ∧ hA1 u = 0} := by
    ext u; constructor
    · rintro ⟨hu, h0⟩
      have hN : trN1 u < 0 := trN1_sign.2 u ⟨hu.1, le_trans hu.2 ang14_lt_pi.le⟩
      exact ⟨hu, by rw [hA1_eq_psiA1 u hN.le, h0]⟩
    · rintro ⟨hu, h0⟩
      have hN : trN1 u < 0 := trN1_sign.2 u ⟨hu.1, le_trans hu.2 ang14_lt_pi.le⟩
      exact ⟨hu, by rw [← hA1_eq_psiA1 u hN.le, h0]⟩
  obtain ⟨hmem, hzero⟩ := sInf_zeroSet_neg_pos hA1 continuous_hA1
    (le_of_lt (lt_trans ang_lt_ang5 ang_lt_ang14)) hA1_ang92 hA1_ang14
  have hdef : yA2 = sInf {u : ℝ | u ∈ Set.Icc (ang (9/2)) (ang 14) ∧ hA1 u = 0} := by
    unfold yA2; rw [hset]
  rw [hdef]
  refine ⟨hmem, ?_⟩
  have hN : trN1 (sInf {u : ℝ | u ∈ Set.Icc (ang (9/2)) (ang 14) ∧ hA1 u = 0}) < 0 :=
    trN1_sign.2 _ ⟨hmem.1.le, le_trans hmem.2.le ang14_lt_pi.le⟩
  rw [← hA1_eq_psiA1 _ hN.le]; exact hzero

lemma psiA1_neg_mid : ∀ u ∈ Set.Icc (ang (5/2)) (ang (9/2)), psiA1 u < 0 := by
  intro u hu
  by_cases h : 0 ≤ trN1 u
  · rw [← gA1_eq_psiA1 u h]
    have hu' : u ∈ Set.Icc (ang (7/10)) (ang (9/2)) := ⟨le_trans ang_lt_ang'.le hu.1, hu.2⟩
    have hb1 : ang (5/2) ∈ Set.Icc (ang (7/10)) (ang (9/2)) := ⟨ang_lt_ang'.le, ang_lt_ang''.le⟩
    have hle := (gA1_anti.le_iff_ge hu' hb1).mpr hu.1
    linarith [hle, gA1_ang52]
  · rw [← hA1_eq_psiA1 u (not_le.mp h).le]
    have hu' : u ∈ Set.Icc (ang (5/2)) Real.pi := ⟨hu.1, le_trans hu.2 ang92_lt_pi.le⟩
    have ha2 : ang (9/2) ∈ Set.Icc (ang (5/2)) Real.pi := ⟨ang_lt_ang''.le, ang92_lt_pi.le⟩
    have hle := (hA1_mono.le_iff_le hu' ha2).mpr hu.2
    linarith [hle, hA1_ang92]


/-! ## Positivity on the left of `ang (7/10)` -/

lemma psiA1_pos_lo (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (ang (7/10))) : 0 < psiA1 u := by
  have hN : (3/4:ℝ) ≤ trN1 u := trN1_lower_left u hu
  have h0 : 0 ≤ trN1 u := le_trans (by norm_num) hN
  rw [← gA1_eq_psiA1 u h0]
  have hb : yclip * (2*(97/100) - trS u) ≤ (177/100) * (2*(97/100) - 682/1000) := by
    have hA : 0 ≤ 2*(97/100) - trS u := by have := trS_le u; linarith
    have hle : 2*(97/100) - trS u ≤ 2*(97/100) - 682/1000 := by linarith [trS_ge u]
    exact mul_le_mul yclip_le hle hA (by norm_num)
  simp only [gA1]
  nlinarith [hb, hN]

/-! ## Membership bookkeeping -/

private lemma yA1_in_Icc9 : yA1 ∈ Set.Icc (ang (7/10)) (ang (9/2)) :=
  ⟨yA1_mem.1.1.le, le_trans yA1_mem.1.2.le ang_lt_ang''.le⟩
private lemma yA2_in_Icc_pi : yA2 ∈ Set.Icc (ang (5/2)) Real.pi :=
  ⟨le_trans ang_lt_ang''.le yA2_mem.1.1.le, le_trans yA2_mem.1.2.le ang14_lt_pi.le⟩

lemma gA1_yA1 : gA1 yA1 = 0 := by
  rw [gA1_eq_psiA1 yA1 (le_of_lt (trN1_sign.1 yA1
    ⟨le_trans ang7_pos.le yA1_mem.1.1.le, yA1_mem.1.2.le⟩))]
  exact yA1_mem.2

lemma hA1_yA2 : hA1 yA2 = 0 := by
  rw [hA1_eq_psiA1 yA2 (le_of_lt (trN1_sign.2 yA2
    ⟨yA2_mem.1.1.le, le_trans yA2_mem.1.2.le ang14_lt_pi.le⟩))]
  exact yA2_mem.2

lemma psiA1_pos_lt_yA1 (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) (h : u < yA1) : 0 < psiA1 u := by
  by_cases hle : u ≤ ang (7/10)
  · exact psiA1_pos_lo u ⟨hu.1, hle⟩
  · have hgt : ang (7/10) < u := not_le.mp hle
    have hN : 0 < trN1 u := trN1_sign.1 u
      ⟨le_trans ang7_pos.le hgt.le, le_trans h.le yA1_mem.1.2.le⟩
    rw [← gA1_eq_psiA1 u hN.le]
    have hu' : u ∈ Set.Icc (ang (7/10)) (ang (9/2)) :=
      ⟨hgt.le, le_trans h.le (le_trans yA1_mem.1.2.le ang_lt_ang''.le)⟩
    have := gA1_anti hu' yA1_in_Icc9 h
    rw [gA1_yA1] at this; exact this

lemma psiA1_pos_gt_yA2 (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) (h : yA2 < u) : 0 < psiA1 u := by
  have hN : trN1 u < 0 := trN1_sign.2 u ⟨le_trans yA2_mem.1.1.le h.le, hu.2⟩
  rw [← hA1_eq_psiA1 u hN.le]
  have hu' : u ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨le_trans ang_lt_ang''.le (le_trans yA2_mem.1.1.le h.le), hu.2⟩
  have hlt := (hA1_mono.lt_iff_lt yA2_in_Icc_pi hu').mpr h
  rw [hA1_yA2] at hlt; exact hlt

lemma psiA1_nonpos_Icc : ∀ u ∈ Set.Icc yA1 yA2, psiA1 u ≤ 0 := by
  intro u hu
  by_cases h52 : u ≤ ang (5/2)
  · have hN : 0 < trN1 u := trN1_sign.1 u
      ⟨le_trans ang7_pos.le (le_trans yA1_mem.1.1.le hu.1), h52⟩
    rw [← gA1_eq_psiA1 u hN.le]
    have hu' : u ∈ Set.Icc (ang (7/10)) (ang (9/2)) :=
      ⟨le_trans yA1_mem.1.1.le hu.1, le_trans h52 ang_lt_ang''.le⟩
    have hle := (gA1_anti.le_iff_ge hu' yA1_in_Icc9).mpr hu.1
    rw [gA1_yA1] at hle; exact hle
  · have hgt : ang (5/2) < u := not_le.mp h52
    by_cases h92 : u ≤ ang (9/2)
    · exact le_of_lt (psiA1_neg_mid u ⟨hgt.le, h92⟩)
    · have hgt9 : ang (9/2) < u := not_le.mp h92
      have hN : trN1 u < 0 := trN1_sign.2 u
        ⟨hgt9.le, le_trans hu.2 (le_trans yA2_mem.1.2.le ang14_lt_pi.le)⟩
      rw [← hA1_eq_psiA1 u hN.le]
      have hu' : u ∈ Set.Icc (ang (5/2)) Real.pi :=
        ⟨hgt.le, le_trans hu.2 (le_trans yA2_mem.1.2.le ang14_lt_pi.le)⟩
      have hle := (hA1_mono.le_iff_le hu' yA2_in_Icc_pi).mpr hu.2
      rw [hA1_yA2] at hle; exact hle

lemma psiA1_neg_Ioo : ∀ u ∈ Set.Ioo yA1 yA2, psiA1 u < 0 := by
  intro u hu
  by_cases h52 : u ≤ ang (5/2)
  · have hN : 0 < trN1 u := trN1_sign.1 u
      ⟨le_trans ang7_pos.le (le_trans yA1_mem.1.1.le hu.1.le), h52⟩
    rw [← gA1_eq_psiA1 u hN.le]
    have hu' : u ∈ Set.Icc (ang (7/10)) (ang (9/2)) :=
      ⟨le_trans yA1_mem.1.1.le hu.1.le, le_trans h52 ang_lt_ang''.le⟩
    have hle := (gA1_anti.lt_iff_gt hu' yA1_in_Icc9).mpr hu.1
    rw [gA1_yA1] at hle; exact hle
  · have hgt : ang (5/2) < u := not_le.mp h52
    by_cases h92 : u ≤ ang (9/2)
    · exact psiA1_neg_mid u ⟨hgt.le, h92⟩
    · have hgt9 : ang (9/2) < u := not_le.mp h92
      have hN : trN1 u < 0 := trN1_sign.2 u
        ⟨hgt9.le, le_trans hu.2.le (le_trans yA2_mem.1.2.le ang14_lt_pi.le)⟩
      rw [← hA1_eq_psiA1 u hN.le]
      have hu' : u ∈ Set.Icc (ang (5/2)) Real.pi :=
        ⟨hgt.le, le_trans hu.2.le (le_trans yA2_mem.1.2.le ang14_lt_pi.le)⟩
      have hle := (hA1_mono.lt_iff_lt hu' yA2_in_Icc_pi).mpr hu.2
      rw [hA1_yA2] at hle; exact hle


/-! ## The sign pattern on `[0, π]` -/

lemma psiA1_le_iff_Icc_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) :
    (psiA1 u ≤ 0 ↔ u ∈ Set.Icc yA1 yA2) := by
  constructor
  · intro h
    by_contra hc
    rw [Set.mem_Icc] at hc; rw [not_and_or] at hc
    rcases hc with hc | hc
    · exact absurd (psiA1_pos_lt_yA1 u hu (not_le.mp hc)) (not_lt.mpr h)
    · exact absurd (psiA1_pos_gt_yA2 u hu (not_le.mp hc)) (not_lt.mpr h)
  · intro h; exact psiA1_nonpos_Icc u h

lemma psiA1_lt_iff_Ioo_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) :
    (psiA1 u < 0 ↔ u ∈ Set.Ioo yA1 yA2) := by
  constructor
  · intro h
    by_contra hc
    rw [Set.mem_Ioo] at hc; rw [not_and_or] at hc
    rcases hc with hc | hc
    · rcases lt_or_eq_of_le (not_lt.mp hc) with hc | hc
      · exact absurd (psiA1_pos_lt_yA1 u hu hc) (not_lt.mpr h.le)
      · rw [hc] at h; exact absurd yA1_mem.2 (ne_of_lt h)
    · rcases lt_or_eq_of_le (not_lt.mp hc) with hc | hc
      · exact absurd (psiA1_pos_gt_yA2 u hu hc) (not_lt.mpr h.le)
      · rw [← hc] at h; exact absurd yA2_mem.2 (ne_of_lt h)
  · intro h; exact psiA1_neg_Ioo u h

lemma psiA1_zero_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) (h : psiA1 u = 0) :
    u = yA1 ∨ u = yA2 := by
  have hle := (psiA1_le_iff_Icc_pi u hu).mp h.le
  by_cases h52 : u ≤ ang (5/2)
  · have hN : 0 < trN1 u := trN1_sign.1 u
      ⟨le_trans ang7_pos.le (le_trans yA1_mem.1.1.le hle.1), h52⟩
    have hu' : u ∈ Set.Icc (ang (7/10)) (ang (9/2)) :=
      ⟨le_trans yA1_mem.1.1.le hle.1, le_trans h52 ang_lt_ang''.le⟩
    have hg : gA1 u = 0 := by rw [gA1_eq_psiA1 u hN.le, h]
    have := (gA1_anti.eq_iff_eq hu' yA1_in_Icc9).mp (hg.trans gA1_yA1.symm)
    exact Or.inl this.symm
  · have hgt : ang (5/2) < u := not_le.mp h52
    by_cases h92 : u ≤ ang (9/2)
    · exact absurd h (ne_of_lt (psiA1_neg_mid u ⟨hgt.le, h92⟩))
    · have hgt9 : ang (9/2) < u := not_le.mp h92
      have hN : trN1 u < 0 := trN1_sign.2 u ⟨hgt9.le, hu.2⟩
      have hu' : u ∈ Set.Icc (ang (5/2)) Real.pi := ⟨hgt.le, hu.2⟩
      have hg : hA1 u = 0 := by rw [hA1_eq_psiA1 u hN.le, h]
      have := (hA1_mono.eq_iff_eq hu' yA2_in_Icc_pi).mp (hg.trans hA1_yA2.symm)
      exact Or.inr this

/-! ## The two lower points -/

private lemma pi_sub_ang (t : ℝ) (ht : 0 < t) : Real.pi - ang t = ang (1/t) := by
  have h : Real.arctan (1/t) = Real.pi/2 - Real.arctan t := by
    rw [one_div]; exact Real.arctan_inv_of_pos ht
  simp only [ang]; rw [h]; ring

lemma ang5_lt_yA2 : ang 5 < yA2 := by
  have h1 : ang 5 ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨le_trans ang_lt_ang''.le ang_lt_ang5.le, le_trans ang_lt_ang14.le ang14_lt_pi.le⟩
  exact (hA1_mono.lt_iff_lt h1 yA2_in_Icc_pi).mp (by rw [hA1_yA2]; exact hA1_ang5)

lemma yA3_eq : yA3 = yA1 + Real.pi := by
  have h23 : Real.pi - ang (3/2) = ang (2/3) := by
    have := pi_sub_ang (3/2) (by norm_num)
    rwa [show (1:ℝ)/(3/2) = 2/3 from by norm_num] at this
  have h52 : Real.pi - ang (2/5) = ang (5/2) := by
    have := pi_sub_ang (2/5) (by norm_num)
    rwa [show (1:ℝ)/(2/5) = 5/2 from by norm_num] at this
  have h1 : 2*Real.pi - ang (3/2) = Real.pi + ang (2/3) := by rw [← h23]; ring
  have h2 : 2*Real.pi - ang (2/5) = Real.pi + ang (5/2) := by rw [← h52]; ring
  have hset : {u : ℝ | u ∈ Set.Icc (2*Real.pi - ang (3/2)) (2*Real.pi - ang (2/5)) ∧ psiA1 u = 0}
      = {yA1 + Real.pi} := by
    ext u; constructor
    · rintro ⟨hu, h0⟩
      rw [Set.mem_singleton_iff]
      rw [Set.mem_Icc, h1, h2] at hu
      have hv : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi := by
        rw [Set.mem_Icc]
        exact ⟨by linarith [hu.1, ang_pos (by norm_num : (0:ℝ) < 2/3)],
               by linarith [hu.2, ang_lt_pi (by norm_num : (0:ℝ) < 5/2)]⟩
      have hper : psiA1 (u - Real.pi) = 0 := by
        have hh := psiA1_period (u - Real.pi); rw [sub_add_cancel] at hh; rw [← hh]; exact h0
      rcases psiA1_zero_pi (u - Real.pi) hv hper with hz | hz
      · linarith [hz]
      · exfalso; linarith [hz, hu.2, yA2_mem.1.1, ang_lt_ang'', ang_lt_ang5]
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc, h1, h2]
        exact ⟨by linarith [ang_lt_ang (show (2:ℝ)/3 < 7/10 by norm_num), yA1_mem.1.1],
               by linarith [yA1_mem.1.2]⟩
      · rw [psiA1_period yA1]; exact yA1_mem.2
  unfold yA3
  rw [hset, csInf_singleton]

lemma yA4_eq : yA4 = yA2 + Real.pi := by
  have h15 : Real.pi - ang (1/5) = ang 5 := by
    have := pi_sub_ang (1/5) (by norm_num)
    rwa [show (1:ℝ)/(1/5) = 5 from by norm_num] at this
  have h115 : Real.pi - ang (1/15) = ang 15 := by
    have := pi_sub_ang (1/15) (by norm_num)
    rwa [show (1:ℝ)/(1/15) = 15 from by norm_num] at this
  have h1 : 2*Real.pi - ang (1/5) = Real.pi + ang 5 := by rw [← h15]; ring
  have h2 : 2*Real.pi - ang (1/15) = Real.pi + ang 15 := by rw [← h115]; ring
  have hset : {u : ℝ | u ∈ Set.Icc (2*Real.pi - ang (1/5)) (2*Real.pi - ang (1/15)) ∧ psiA1 u = 0}
      = {yA2 + Real.pi} := by
    ext u; constructor
    · rintro ⟨hu, h0⟩
      rw [Set.mem_singleton_iff]
      rw [Set.mem_Icc, h1, h2] at hu
      have hv : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi := by
        rw [Set.mem_Icc]
        exact ⟨by linarith [hu.1, ang_pos (by norm_num : (0:ℝ) < 5)],
               by linarith [hu.2, ang_lt_pi (by norm_num : (0:ℝ) < 15)]⟩
      have hper : psiA1 (u - Real.pi) = 0 := by
        have hh := psiA1_period (u - Real.pi); rw [sub_add_cancel] at hh; rw [← hh]; exact h0
      rcases psiA1_zero_pi (u - Real.pi) hv hper with hz | hz
      · exfalso; linarith [hz, hu.1, yA1_mem.1.2, ang_lt_ang'', ang_lt_ang5]
      · linarith [hz]
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc, h1, h2]
        exact ⟨by linarith [ang5_lt_yA2],
               by have := ang_lt_ang (show (14:ℝ) < 15 by norm_num); linarith [yA2_mem.1.2, this]⟩
      · rw [psiA1_period yA2]; exact yA2_mem.2
  unfold yA4
  rw [hset, csInf_singleton]


/-! ## Angle rewrites -/

private lemma pi_sub_ang' (t : ℝ) (ht : 0 < t) : Real.pi - ang t = ang (1/t) := pi_sub_ang t ht

lemma two_pi_sub_ang_three_halves : 2*Real.pi - ang (3/2) = Real.pi + ang (2/3) := by
  have := pi_sub_ang' (3/2) (by norm_num)
  rw [show (1:ℝ)/(3/2) = 2/3 from by norm_num] at this
  rw [← this]; ring

lemma two_pi_sub_ang_two_fifths : 2*Real.pi - ang (2/5) = Real.pi + ang (5/2) := by
  have := pi_sub_ang' (2/5) (by norm_num)
  rw [show (1:ℝ)/(2/5) = 5/2 from by norm_num] at this
  rw [← this]; ring

lemma two_pi_sub_ang_one_fifth : 2*Real.pi - ang (1/5) = Real.pi + ang 5 := by
  have := pi_sub_ang' (1/5) (by norm_num)
  rw [show (1:ℝ)/(1/5) = 5 from by norm_num] at this
  rw [← this]; ring

lemma two_pi_sub_ang_one_fifteenth : 2*Real.pi - ang (1/15) = Real.pi + ang 15 := by
  have := pi_sub_ang' (1/15) (by norm_num)
  rw [show (1:ℝ)/(1/15) = 15 from by norm_num] at this
  rw [← this]; ring

/-! ## The main theorem -/

theorem psiA1_shape :
    (Work.BoxShrink.PinchOff.RefuteDrop.yA1 < Work.BoxShrink.PinchOff.RefuteDrop.yA2 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.yA2 < Work.BoxShrink.PinchOff.RefuteDrop.yA3 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.yA3 < Work.BoxShrink.PinchOff.RefuteDrop.yA4 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.yA4 < 2 * Real.pi) ∧
      (Work.BoxShrink.PinchOff.RefuteDrop.yA1 ∈ Set.Ioo (Work.BoxShrink.PinchOff.RefuteDrop.ang (7/10)) (Work.BoxShrink.PinchOff.RefuteDrop.ang (5/2)) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.yA2 ∈ Set.Ioo (Work.BoxShrink.PinchOff.RefuteDrop.ang (9/2)) (Work.BoxShrink.PinchOff.RefuteDrop.ang 14) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.yA3 ∈ Set.Ioo (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (3/2)) (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (2/5)) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.yA4 ∈ Set.Ioo (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (1/5)) (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (1/15))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (Work.BoxShrink.PinchOff.RefuteDrop.psiA1 u ≤ 0 ↔
          u ∈ Set.Icc Work.BoxShrink.PinchOff.RefuteDrop.yA1 Work.BoxShrink.PinchOff.RefuteDrop.yA2 ∪ Set.Icc Work.BoxShrink.PinchOff.RefuteDrop.yA3 Work.BoxShrink.PinchOff.RefuteDrop.yA4)) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (Work.BoxShrink.PinchOff.RefuteDrop.psiA1 u < 0 ↔
          u ∈ Set.Ioo Work.BoxShrink.PinchOff.RefuteDrop.yA1 Work.BoxShrink.PinchOff.RefuteDrop.yA2 ∪ Set.Ioo Work.BoxShrink.PinchOff.RefuteDrop.yA3 Work.BoxShrink.PinchOff.RefuteDrop.yA4)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨yA1_mem.1, yA2_mem.1, ?_, ?_⟩, ?_, ?_⟩
  · exact lt_trans yA1_mem.1.2 (lt_trans ang_lt_ang'' yA2_mem.1.1)
  · rw [yA3_eq]
    exact lt_trans (lt_trans yA2_mem.1.2 ang14_lt_pi) (by linarith [yA1_mem.1.1, ang7_pos])
  · rw [yA3_eq, yA4_eq]
    linarith [lt_trans yA1_mem.1.2 (lt_trans ang_lt_ang'' yA2_mem.1.1)]
  · rw [yA4_eq]
    linarith [yA2_mem.1.2, ang14_lt_pi, Real.pi_pos]
  · rw [yA3_eq, two_pi_sub_ang_three_halves, two_pi_sub_ang_two_fifths]
    exact ⟨by linarith [ang_lt_ang (show (2:ℝ)/3 < 7/10 by norm_num), yA1_mem.1.1],
           by linarith [yA1_mem.1.2]⟩
  · rw [yA4_eq, two_pi_sub_ang_one_fifth, two_pi_sub_ang_one_fifteenth]
    exact ⟨by linarith [ang5_lt_yA2],
           by have := ang_lt_ang (show (14:ℝ) < 15 by norm_num); linarith [yA2_mem.1.2, this]⟩
  · intro u hu
    rw [yA3_eq, yA4_eq]
    constructor
    · intro h
      by_cases hup : u ≤ Real.pi
      · exact Or.inl ((psiA1_le_iff_Icc_pi u ⟨hu.1, hup⟩).mp h)
      · refine Or.inr ⟨?_, ?_⟩
        · have hper : psiA1 (u - Real.pi) ≤ 0 := by
            have hh := psiA1_period (u - Real.pi); rw [sub_add_cancel] at hh; rw [← hh]; exact h
          have hvv : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi :=
            ⟨by linarith [not_le.mp hup], by linarith [hu.2]⟩
          have := (psiA1_le_iff_Icc_pi (u - Real.pi) hvv).mp hper
          linarith [this.1]
        · have hper : psiA1 (u - Real.pi) ≤ 0 := by
            have hh := psiA1_period (u - Real.pi); rw [sub_add_cancel] at hh; rw [← hh]; exact h
          have hvv : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi :=
            ⟨by linarith [not_le.mp hup], by linarith [hu.2]⟩
          have := (psiA1_le_iff_Icc_pi (u - Real.pi) hvv).mp hper
          linarith [this.2]
    · rintro (h | h)
      · have hup : u ≤ Real.pi := le_trans h.2 (le_trans yA2_mem.1.2.le ang14_lt_pi.le)
        exact (psiA1_le_iff_Icc_pi u ⟨hu.1, hup⟩).mpr h
      · have hv : u - Real.pi ∈ Set.Icc yA1 yA2 := ⟨by linarith [h.1], by linarith [h.2]⟩
        have hv' : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi :=
          ⟨le_trans ang7_pos.le (le_trans yA1_mem.1.1.le hv.1),
           le_trans (le_trans hv.2 yA2_mem.1.2.le) ang14_lt_pi.le⟩
        have := (psiA1_le_iff_Icc_pi (u - Real.pi) hv').mpr hv
        rw [psiA1_sub_pi u]; exact this
  · intro u hu
    rw [yA3_eq, yA4_eq]
    constructor
    · intro h
      by_cases hup : u ≤ Real.pi
      · exact Or.inl ((psiA1_lt_iff_Ioo_pi u ⟨hu.1, hup⟩).mp h)
      · refine Or.inr ⟨?_, ?_⟩
        · have hper : psiA1 (u - Real.pi) < 0 := by
            have hh := psiA1_period (u - Real.pi); rw [sub_add_cancel] at hh; rw [← hh]; exact h
          have hvv : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi :=
            ⟨by linarith [not_le.mp hup], by linarith [hu.2]⟩
          have := (psiA1_lt_iff_Ioo_pi (u - Real.pi) hvv).mp hper
          linarith [this.1]
        · have hper : psiA1 (u - Real.pi) < 0 := by
            have hh := psiA1_period (u - Real.pi); rw [sub_add_cancel] at hh; rw [← hh]; exact h
          have hvv : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi :=
            ⟨by linarith [not_le.mp hup], by linarith [hu.2]⟩
          have := (psiA1_lt_iff_Ioo_pi (u - Real.pi) hvv).mp hper
          linarith [this.2]
    · rintro (h | h)
      · have hup : u < Real.pi := lt_trans h.2 (lt_trans yA2_mem.1.2 ang14_lt_pi)
        exact (psiA1_lt_iff_Ioo_pi u ⟨hu.1, hup.le⟩).mpr h
      · have hv : u - Real.pi ∈ Set.Ioo yA1 yA2 := ⟨by linarith [h.1], by linarith [h.2]⟩
        have hv' : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi :=
          ⟨le_trans ang7_pos.le (le_trans yA1_mem.1.1.le hv.1.le),
           le_trans (le_trans hv.2.le yA2_mem.1.2.le) ang14_lt_pi.le⟩
        have := (psiA1_lt_iff_Ioo_pi (u - Real.pi) hv').mpr hv
        rw [psiA1_sub_pi u]; exact this

end Work.RefuteDrop
