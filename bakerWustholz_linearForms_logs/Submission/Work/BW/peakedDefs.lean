import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped ENNReal

namespace Work.BW

/-- The 1-D Gaussian density `exp (-π x²)` (the density of `gaussianReal 0 ⟨1/(2π)⟩`). -/
noncomputable def gd : ℝ → ℝ := fun x => Real.exp (-(Real.pi * x ^ 2))

/-- The 1-D uniform density of the unit interval `[-1/2, 1/2]`. -/
noncomputable def ud : ℝ → ℝ := Set.indicator (Set.Icc (-1/2 : ℝ) (1/2)) (fun _ => (1 : ℝ))

lemma gd_meas : Measurable gd := by unfold gd; fun_prop

lemma gd_even (x : ℝ) : gd (-x) = gd x := by unfold gd; rw [neg_sq]

lemma gd_nn (x : ℝ) : 0 ≤ gd x := by unfold gd; positivity

lemma gd_anti : AntitoneOn gd (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold gd
  apply Real.exp_le_exp.mpr
  have h2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  nlinarith [Real.pi_pos]

lemma gd_int : Integrable gd := by
  have h := integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
  have h2 : Integrable (fun x : ℝ => Real.exp (-(Real.pi * x ^ 2))) := by
    simpa [neg_mul] using h
  exact h2

lemma integral_gd : ∫ x, gd x = 1 := by
  have h := integral_gaussian Real.pi
  rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one] at h
  simp only [gd]
  convert h using 2
  ring_nf

lemma ud_meas : Measurable ud := by
  unfold ud; exact measurable_const.indicator measurableSet_Icc

lemma ud_even (x : ℝ) : ud (-x) = ud x := by
  unfold ud
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases h : x ∈ Set.Icc (-1/2 : ℝ) (1/2)
  · have h' : -x ∈ Set.Icc (-1/2 : ℝ) (1/2) := by
      simp only [Set.mem_Icc] at h ⊢; exact ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [if_pos h', if_pos h]
  · have h' : -x ∉ Set.Icc (-1/2 : ℝ) (1/2) := by
      intro hh; apply h
      simp only [Set.mem_Icc] at hh ⊢; exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
    rw [if_neg h', if_neg h]

lemma ud_nn (x : ℝ) : 0 ≤ ud x := by
  unfold ud
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma ud_anti : AntitoneOn ud (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold ud
  by_cases hb' : b ≤ (1/2 : ℝ)
  · have ha' : a ≤ (1/2 : ℝ) := le_trans hab hb'
    rw [Set.indicator_of_mem (show a ∈ Set.Icc (-1/2 : ℝ) (1/2) from ⟨by linarith [ha], ha'⟩),
        Set.indicator_of_mem (show b ∈ Set.Icc (-1/2 : ℝ) (1/2) from ⟨by linarith [hb], hb'⟩)]
  · have hb'' : b ∉ Set.Icc (-1/2 : ℝ) (1/2) := by intro h; exact hb' h.2
    rw [Set.indicator_of_notMem hb'']
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) a

lemma ud_int : Integrable ud := by
  rw [ud, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)


lemma gaussianPDFReal_gd (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 (⟨1/(2*Real.pi), by positivity⟩ : NNReal) x = gd x := by
  show (Real.sqrt (2 * Real.pi * ((⟨1/(2*Real.pi), by positivity⟩ : NNReal) : ℝ)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * ((⟨1/(2*Real.pi), by positivity⟩ : NNReal) : ℝ)))
      = Real.exp (-(Real.pi * x ^ 2))
  have hsqrt : Real.sqrt (2 * Real.pi * (1/(2*Real.pi))) = 1 := by
    have h : (2:ℝ) * Real.pi * (1/(2*Real.pi)) = 1 := by field_simp
    rw [h, Real.sqrt_one]
  have hden : (2:ℝ) * (1/(2*Real.pi)) = 1/Real.pi := by field_simp
  rw [hsqrt, inv_one, one_mul, hden, sub_zero]
  congr 1
  field_simp

end Work.BW
