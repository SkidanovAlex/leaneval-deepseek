import Mathlib
import Submission.Commons.NumberTheory.Linnik.Ksum_positivity

open scoped BigOperators
open Commons.NumberTheory.Linnik (re_div_cpow_eq mul_re_mul_re star_apply_eq_inv star_cpow_ofReal_neg)

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.ZeroFreeTables

theorem triple_re_mul_re (a b c : ℂ) :
    a.re * b.re * c.re = (1/4) * (a*b*c).re + (1/4) * (a*b*star c).re
      + (1/4) * (a*star b*c).re + (1/4) * (star a*b*c).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem Ksum_three_pointwise_aux {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    {L β γ₁ γ₂ γ₃ : ℝ} (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₃ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₃ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₃⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₂ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₂ * χ₃⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  set a₁ : ℂ := χ₁ (n : ZMod q) * (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) with ha₁
  set a₂ : ℂ := χ₂ (n : ZMod q) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) with ha₂
  set a₃ : ℂ := χ₃ (n : ZMod q) * (n : ℂ) ^ (-((γ₃ : ℂ) * Complex.I)) with ha₃
  set p : ℝ := ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re with hp
  have hq01 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 ∨
      ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
    by_cases h : IsUnit (n : ZMod q)
    · right; rw [← h.unit_spec]; exact MulChar.one_apply h
    · left; exact MulChar.map_nonunit (1 : DirichletCharacter ℂ q) h
  have hp01 : p = 0 ∨ p = 1 := by
    rcases hq01 with h | h
    · left; rw [hp, h]; simp
    · right; rw [hp, h]; simp
  have hnu : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 → ¬ IsUnit (n : ZMod q) := by
    intro h hunit
    have h1 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
      rw [← hunit.unit_spec]; exact MulChar.one_apply hunit
    rw [h] at h1; exact zero_ne_one h1
  have hp0 : p = 0 → ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 := by
    intro h0
    rcases hq01 with h | h
    · exact h
    · exfalso; rw [hp, h] at h0; norm_num at h0
  have hχ10 : p = 0 → a₁ = 0 := by
    intro h0; rw [ha₁, MulChar.map_nonunit χ₁ (hnu (hp0 h0)), zero_mul]
  have hχ20 : p = 0 → a₂ = 0 := by
    intro h0; rw [ha₂, MulChar.map_nonunit χ₂ (hnu (hp0 h0)), zero_mul]
  have hχ30 : p = 0 → a₃ = 0 := by
    intro h0; rw [ha₃, MulChar.map_nonunit χ₃ (hnu (hp0 h0)), zero_mul]
  have e0 : (((1 : DirichletCharacter ℂ q)) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
      = (n : ℝ) ^ (-β) * p := by
    have h := re_div_cpow_eq (1 : DirichletCharacter ℂ q) hn β 0
    simp only [add_zero, neg_zero, Complex.cpow_zero, mul_one] at h
    rw [h, hp]
  have e1 : (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₁.re := by
    rw [re_div_cpow_eq χ₁ hn β ((γ₁ : ℂ) * Complex.I), ha₁]
  have e2 : (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₂.re := by
    rw [re_div_cpow_eq χ₂ hn β ((γ₂ : ℂ) * Complex.I), ha₂]
  have e3 : (χ₃ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₃ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₃.re := by
    rw [re_div_cpow_eq χ₃ hn β ((γ₃ : ℂ) * Complex.I), ha₃]
  have hsp12 : (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsp12m : (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ ((γ₂ : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsp13 : (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₃ : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsp13m : (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ ((γ₃ : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsp23 : (n : ℂ) ^ (-(((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₃ : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsp23m : (n : ℂ) ^ (-(((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) * (n : ℂ) ^ ((γ₃ : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hA12 : (χ₁ * χ₂) (n : ZMod q) * (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I))
      = a₁ * a₂ := by
    rw [ha₁, ha₂, MulChar.mul_apply, hsp12]; ring
  have hB12 : (χ₁ * χ₂⁻¹) (n : ZMod q) * (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I))
      = a₁ * star a₂ := by
    rw [ha₁, ha₂, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₂,
      star_cpow_ofReal_neg hn γ₂, hsp12m]; ring
  have hA13 : (χ₁ * χ₃) (n : ZMod q) * (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = a₁ * a₃ := by
    rw [ha₁, ha₃, MulChar.mul_apply, hsp13]; ring
  have hB13 : (χ₁ * χ₃⁻¹) (n : ZMod q) * (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I))
      = a₁ * star a₃ := by
    rw [ha₁, ha₃, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₃,
      star_cpow_ofReal_neg hn γ₃, hsp13m]; ring
  have hA23 : (χ₂ * χ₃) (n : ZMod q) * (n : ℂ) ^ (-(((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = a₂ * a₃ := by
    rw [ha₂, ha₃, MulChar.mul_apply, hsp23]; ring
  have hB23 : (χ₂ * χ₃⁻¹) (n : ZMod q) * (n : ℂ) ^ (-(((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I))
      = a₂ * star a₃ := by
    rw [ha₂, ha₃, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₃,
      star_cpow_ofReal_neg hn γ₃, hsp23m]; ring
  have hsp123 : (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I))
        * (n : ℂ) ^ (-((γ₃ : ℂ) * Complex.I)) := by
    rw [show -(((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (-((γ₁ : ℂ) * Complex.I)) + (-(((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)) from by ring,
      Complex.cpow_add _ _ hnc, hsp23]
    ring
  have hsp123m : (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I))
        * (n : ℂ) ^ ((γ₃ : ℂ) * Complex.I) := by
    rw [show -(((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)
        = (-((γ₁ : ℂ) * Complex.I)) + (-(((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)) from by ring,
      Complex.cpow_add _ _ hnc, hsp23m]
    ring
  have hsp12m3 : (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ ((γ₂ : ℂ) * Complex.I)
        * (n : ℂ) ^ (-((γ₃ : ℂ) * Complex.I)) := by
    rw [show -(((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (-((γ₁ : ℂ) * Complex.I)) + (((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) from by ring,
      Complex.cpow_add _ _ hnc,
      show (((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)
        = ((γ₂ : ℂ) * Complex.I) + (-((γ₃ : ℂ) * Complex.I)) from by ring,
      Complex.cpow_add _ _ hnc]
    ring
  have hspm123 : (n : ℂ) ^ (-((-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I))
      = (n : ℂ) ^ ((γ₁ : ℂ) * Complex.I) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I))
        * (n : ℂ) ^ (-((γ₃ : ℂ) * Complex.I)) := by
    rw [show -((-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = ((γ₁ : ℂ) * Complex.I) + (-(((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)) from by ring,
      Complex.cpow_add _ _ hnc, hsp23]
    ring
  have hA123 : (χ₁ * χ₂ * χ₃) (n : ZMod q)
      * (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)) = a₁ * a₂ * a₃ := by
    rw [ha₁, ha₂, ha₃, MulChar.mul_apply, MulChar.mul_apply, hsp123]; ring
  have hB123 : (χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q)
      * (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)) = a₁ * a₂ * star a₃ := by
    rw [ha₁, ha₂, ha₃, MulChar.mul_apply, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₃,
      star_cpow_ofReal_neg hn γ₃, hsp123m]; ring
  have hC123 : (χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q)
      * (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)) = a₁ * star a₂ * a₃ := by
    rw [ha₁, ha₂, ha₃, MulChar.mul_apply, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₂,
      star_cpow_ofReal_neg hn γ₂, hsp12m3]; ring
  have hD123 : (χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q)
      * (n : ℂ) ^ (-((-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)) = star a₁ * a₂ * a₃ := by
    rw [ha₁, ha₂, ha₃, MulChar.mul_apply, MulChar.mul_apply, star_mul, star_apply_eq_inv χ₁,
      star_cpow_ofReal_neg hn γ₁, hspm123]; ring
  have e4 : ((χ₁ * χ₂) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₂).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂) hn β (((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I), hA12]
  have e5 : ((χ₁ * χ₂⁻¹) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * star a₂).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂⁻¹) hn β (((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I), hB12]
  have e6 : ((χ₁ * χ₃) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₃).re := by
    rw [re_div_cpow_eq (χ₁ * χ₃) hn β (((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I), hA13]
  have e7 : ((χ₁ * χ₃⁻¹) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * star a₃).re := by
    rw [re_div_cpow_eq (χ₁ * χ₃⁻¹) hn β (((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I), hB13]
  have e8 : ((χ₂ * χ₃) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₂ * a₃).re := by
    rw [re_div_cpow_eq (χ₂ * χ₃) hn β (((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I), hA23]
  have e9 : ((χ₂ * χ₃⁻¹) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₂ * star a₃).re := by
    rw [re_div_cpow_eq (χ₂ * χ₃⁻¹) hn β (((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I), hB23]
  have e10 : ((χ₁ * χ₂ * χ₃) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₂ * a₃).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂ * χ₃) hn β (((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I), hA123]
  have e11 : ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₂ * star a₃).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂ * χ₃⁻¹) hn β (((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I), hB123]
  have e12 : ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * star a₂ * a₃).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂⁻¹ * χ₃) hn β (((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I), hC123]
  have e13 : ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q)
      / (n : ℂ) ^ ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (star a₁ * a₂ * a₃).re := by
    rw [re_div_cpow_eq (χ₁⁻¹ * χ₂ * χ₃) hn β ((-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I), hD123]
  have hid : (p + a₁.re) * (p + a₂.re) * (p + a₃.re)
      = p + a₁.re + a₂.re + a₃.re
        + ((1/2) * (a₁ * a₂).re + (1/2) * (a₁ * star a₂).re)
        + ((1/2) * (a₁ * a₃).re + (1/2) * (a₁ * star a₃).re)
        + ((1/2) * (a₂ * a₃).re + (1/2) * (a₂ * star a₃).re)
        + ((1/4) * (a₁ * a₂ * a₃).re + (1/4) * (a₁ * a₂ * star a₃).re
            + (1/4) * (a₁ * star a₂ * a₃).re + (1/4) * (star a₁ * a₂ * a₃).re) := by
    rcases hp01 with h | h
    · rw [h, hχ10 h, hχ20 h, hχ30 h]; simp
    · rw [h, ← mul_re_mul_re a₁ a₂, ← mul_re_mul_re a₁ a₃, ← mul_re_mul_re a₂ a₃,
        ← triple_re_mul_re a₁ a₂ a₃]
      ring
  have hmain : (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₃ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₃ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₃⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₂ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₂ * χ₃⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re
            * f (Real.log n / L))
      = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
        * ((p + a₁.re) * (p + a₂.re) * (p + a₃.re)) := by
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, hid]
    ring
  have hnorm₁ : ‖a₁‖ ≤ 1 := by
    rw [ha₁, norm_mul]
    refine mul_le_one₀ (DirichletCharacter.norm_le_one χ₁ _) (norm_nonneg _) ?_
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hnorm₂ : ‖a₂‖ ≤ 1 := by
    rw [ha₂, norm_mul]
    refine mul_le_one₀ (DirichletCharacter.norm_le_one χ₂ _) (norm_nonneg _) ?_
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hnorm₃ : ‖a₃‖ ≤ 1 := by
    rw [ha₃, norm_mul]
    refine mul_le_one₀ (DirichletCharacter.norm_le_one χ₃ _) (norm_nonneg _) ?_
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hfac₁ : 0 ≤ p + a₁.re := by
    rcases hp01 with h | h
    · rw [h, hχ10 h]; simp
    · rw [h]
      have hle := Complex.abs_re_le_norm a₁
      rw [abs_le] at hle
      linarith [hle.1, hnorm₁]
  have hfac₂ : 0 ≤ p + a₂.re := by
    rcases hp01 with h | h
    · rw [h, hχ20 h]; simp
    · rw [h]
      have hle := Complex.abs_re_le_norm a₂
      rw [abs_le] at hle
      linarith [hle.1, hnorm₂]
  have hfac₃ : 0 ≤ p + a₃.re := by
    rcases hp01 with h | h
    · rw [h, hχ30 h]; simp
    · rw [h]
      have hle := Complex.abs_re_le_norm a₃
      rw [abs_le] at hle
      linarith [hle.1, hnorm₃]
  have hprod : 0 ≤ (p + a₁.re) * (p + a₂.re) * (p + a₃.re) :=
    mul_nonneg (mul_nonneg hfac₁ hfac₂) hfac₃
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by positivity
  have hff : 0 ≤ f (Real.log n / L) := hf _
  have hnb : 0 ≤ (n : ℝ) ^ (-β) := Real.rpow_nonneg hnpos.le _
  rw [hmain]
  exact mul_nonneg (mul_nonneg (mul_nonneg hΛ hff) hnb) hprod

theorem Ksum_positivity_three {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    {x₀ L β γ₁ γ₂ γ₃ : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) :
    0 ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ₃ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₃ : ℂ) * Complex.I)).re * f (Real.log n / L))
      + (1/2) * ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L)))
      + (1/4) * ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L))) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    refine ⟨Nat.ceil (Real.exp (x₀ * L)) + 1, fun n hn => ?_⟩
    have h1 : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have : (Nat.ceil (Real.exp (x₀ * L)) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hn)
      exact le_trans (Nat.le_ceil _) this
    have h2 : x₀ * L ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hL]
    linarith
  have hvan : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := fun n hn => hsupp _ (hN n hn)
  set s0 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L) with hs0
  set s1 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re * f (Real.log n / L) with hs1
  set s2 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / L) with hs2
  set s3 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₃ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₃ : ℂ) * Complex.I)).re * f (Real.log n / L) with hs3
  set s4 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs4
  set s5 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs5
  set s6 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs6
  set s7 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs7
  set s8 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs8
  set s9 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs9
  set s10 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs10
  set s11 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs11
  set s12 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs12
  set s13 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)).re * f (Real.log n / L) with hs13
  have hz0 : ∀ n : ℕ, N ≤ n → s0 n = 0 := by intro n hn; simp only [hs0, hvan n hn]; ring
  have hz1 : ∀ n : ℕ, N ≤ n → s1 n = 0 := by intro n hn; simp only [hs1, hvan n hn]; ring
  have hz2 : ∀ n : ℕ, N ≤ n → s2 n = 0 := by intro n hn; simp only [hs2, hvan n hn]; ring
  have hz3 : ∀ n : ℕ, N ≤ n → s3 n = 0 := by intro n hn; simp only [hs3, hvan n hn]; ring
  have hz4 : ∀ n : ℕ, N ≤ n → s4 n = 0 := by intro n hn; simp only [hs4, hvan n hn]; ring
  have hz5 : ∀ n : ℕ, N ≤ n → s5 n = 0 := by intro n hn; simp only [hs5, hvan n hn]; ring
  have hz6 : ∀ n : ℕ, N ≤ n → s6 n = 0 := by intro n hn; simp only [hs6, hvan n hn]; ring
  have hz7 : ∀ n : ℕ, N ≤ n → s7 n = 0 := by intro n hn; simp only [hs7, hvan n hn]; ring
  have hz8 : ∀ n : ℕ, N ≤ n → s8 n = 0 := by intro n hn; simp only [hs8, hvan n hn]; ring
  have hz9 : ∀ n : ℕ, N ≤ n → s9 n = 0 := by intro n hn; simp only [hs9, hvan n hn]; ring
  have hz10 : ∀ n : ℕ, N ≤ n → s10 n = 0 := by intro n hn; simp only [hs10, hvan n hn]; ring
  have hz11 : ∀ n : ℕ, N ≤ n → s11 n = 0 := by intro n hn; simp only [hs11, hvan n hn]; ring
  have hz12 : ∀ n : ℕ, N ≤ n → s12 n = 0 := by intro n hn; simp only [hs12, hvan n hn]; ring
  have hz13 : ∀ n : ℕ, N ≤ n → s13 n = 0 := by intro n hn; simp only [hs13, hvan n hn]; ring
  have ht0 : (∑' n : ℕ, s0 n) = ∑ n ∈ Finset.range N, s0 n := tsum_eq_sum (fun n hn => hz0 n (by simpa using hn))
  have ht1 : (∑' n : ℕ, s1 n) = ∑ n ∈ Finset.range N, s1 n := tsum_eq_sum (fun n hn => hz1 n (by simpa using hn))
  have ht2 : (∑' n : ℕ, s2 n) = ∑ n ∈ Finset.range N, s2 n := tsum_eq_sum (fun n hn => hz2 n (by simpa using hn))
  have ht3 : (∑' n : ℕ, s3 n) = ∑ n ∈ Finset.range N, s3 n := tsum_eq_sum (fun n hn => hz3 n (by simpa using hn))
  have ht4 : (∑' n : ℕ, s4 n) = ∑ n ∈ Finset.range N, s4 n := tsum_eq_sum (fun n hn => hz4 n (by simpa using hn))
  have ht5 : (∑' n : ℕ, s5 n) = ∑ n ∈ Finset.range N, s5 n := tsum_eq_sum (fun n hn => hz5 n (by simpa using hn))
  have ht6 : (∑' n : ℕ, s6 n) = ∑ n ∈ Finset.range N, s6 n := tsum_eq_sum (fun n hn => hz6 n (by simpa using hn))
  have ht7 : (∑' n : ℕ, s7 n) = ∑ n ∈ Finset.range N, s7 n := tsum_eq_sum (fun n hn => hz7 n (by simpa using hn))
  have ht8 : (∑' n : ℕ, s8 n) = ∑ n ∈ Finset.range N, s8 n := tsum_eq_sum (fun n hn => hz8 n (by simpa using hn))
  have ht9 : (∑' n : ℕ, s9 n) = ∑ n ∈ Finset.range N, s9 n := tsum_eq_sum (fun n hn => hz9 n (by simpa using hn))
  have ht10 : (∑' n : ℕ, s10 n) = ∑ n ∈ Finset.range N, s10 n := tsum_eq_sum (fun n hn => hz10 n (by simpa using hn))
  have ht11 : (∑' n : ℕ, s11 n) = ∑ n ∈ Finset.range N, s11 n := tsum_eq_sum (fun n hn => hz11 n (by simpa using hn))
  have ht12 : (∑' n : ℕ, s12 n) = ∑ n ∈ Finset.range N, s12 n := tsum_eq_sum (fun n hn => hz12 n (by simpa using hn))
  have ht13 : (∑' n : ℕ, s13 n) = ∑ n ∈ Finset.range N, s13 n := tsum_eq_sum (fun n hn => hz13 n (by simpa using hn))
  have hterm : ∀ n ∈ Finset.range N,
      0 ≤ s0 n + s1 n + s2 n + s3 n
          + (1/2) * s4 n + (1/2) * s5 n + (1/2) * s6 n + (1/2) * s7 n + (1/2) * s8 n + (1/2) * s9 n
          + (1/4) * s10 n + (1/4) * s11 n + (1/4) * s12 n + (1/4) * s13 n := by
    intro n hn
    rw [Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hL0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
      simp only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13]
      rw [hL0]
      norm_num
    · simpa only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13]
        using Ksum_three_pointwise_aux (q := q) hf (L := L) (β := β) (γ₁ := γ₁) (γ₂ := γ₂) (γ₃ := γ₃)
          χ₁ χ₂ χ₃ h
  have hcomb : (∑ n ∈ Finset.range N, (s0 n + s1 n + s2 n + s3 n
        + (1/2) * s4 n + (1/2) * s5 n + (1/2) * s6 n + (1/2) * s7 n + (1/2) * s8 n + (1/2) * s9 n
        + (1/4) * s10 n + (1/4) * s11 n + (1/4) * s12 n + (1/4) * s13 n))
      = (∑ n ∈ Finset.range N, s0 n) + (∑ n ∈ Finset.range N, s1 n)
        + (∑ n ∈ Finset.range N, s2 n) + (∑ n ∈ Finset.range N, s3 n)
        + (1/2) * ((∑ n ∈ Finset.range N, s4 n) + (∑ n ∈ Finset.range N, s5 n)
            + (∑ n ∈ Finset.range N, s6 n) + (∑ n ∈ Finset.range N, s7 n)
            + (∑ n ∈ Finset.range N, s8 n) + (∑ n ∈ Finset.range N, s9 n))
        + (1/4) * ((∑ n ∈ Finset.range N, s10 n) + (∑ n ∈ Finset.range N, s11 n)
            + (∑ n ∈ Finset.range N, s12 n) + (∑ n ∈ Finset.range N, s13 n)) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ← hcomb]
  exact Finset.sum_nonneg hterm

end Work.ZeroFreeTables
