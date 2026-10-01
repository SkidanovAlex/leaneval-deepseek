import Mathlib
import Submission.Work.LinnikAreas.DhK.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le

open scoped Classical BigOperators Topology
open Complex Filter

namespace Work.LinnikAreas.DhK

noncomputable section

set_option maxHeartbeats 0

lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 := by
  intro h; rw [h] at hs; norm_num at hs

lemma ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h; rw [h] at hs; norm_num at hs

lemma isOpen_re_gt_one : IsOpen {z : ℂ | (1 : ℝ) < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s.Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : s.re = -2 * (n : ℝ) := by rw [hn]; simp
  rw [hre] at hs
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma Gammaℝ_add_one_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (s + 1).Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : (s + 1).re = -2 * (n : ℝ) := by rw [hn]; simp
  simp only [Complex.add_re, Complex.one_re] at hre
  rw [show s.re = -2 * (n : ℝ) - 1 by linarith] at hs
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma Xi_eq_half_mul (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  rw [Xi, completedRiemannZeta_eq]
  field_simp
  ring

lemma Xi_eventuallyEq_half_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Xi =ᶠ[𝓝 s] fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z := by
  filter_upwards [isOpen_ne.mem_nhds h0, isOpen_ne.mem_nhds h1] with z hz0 hz1
  exact Xi_eq_half_mul z hz0 hz1

lemma Xi_eq_head_mul {s : ℂ} (hs : 1 < s.re) :
    Xi s = ((1 / 2 : ℂ) * s * (s - 1)) * (riemannZeta s * s.Gammaℝ) := by
  have h0 := ne_zero_of_one_lt_re hs
  have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [Xi_eq_half_mul s h0 (ne_one_of_one_lt_re hs), riemannZeta_def_of_ne_zero h0]
  rw [div_mul_cancel₀ _ hG]

lemma logDeriv_sub_one (s : ℂ) (hs : s - 1 ≠ 0) :
    logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
  rw [logDeriv_apply]
  have hder : deriv (fun z : ℂ => z - 1) s = 1 := by
    have h1 : (fun z : ℂ => z - 1) = fun z => z + (-1 : ℂ) := by funext z; ring
    rw [h1]
    simp
  rw [hder, one_div]

lemma logDeriv_head (s : ℂ) (hs0 : s ≠ 0) (hs1 : s - 1 ≠ 0) :
    logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
  have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := logDeriv_sub_one s hs1
  have hid : logDeriv (fun z : ℂ => z) s = 1 / s := logDeriv_id s
  have hpar : logDeriv (fun z : ℂ => z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
    have hm := logDeriv_mul (x := s) (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
      hs0 hs1 (by fun_prop) (by fun_prop)
    erw [hm]; rw [hid, h2]
  calc logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s
      = logDeriv (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1))) s := by
        congr 1; funext z; ring
    _ = logDeriv (fun z : ℂ => z * (z - 1)) s :=
        logDeriv_const_mul (f := fun z : ℂ => z * (z - 1)) (x := s) (1 / 2 : ℂ)
          (by norm_num)
    _ = 1 / s + 1 / (s - 1) := hpar

lemma Xi_logDeriv (s : ℂ) (hs : 1 < s.re) :
    logDeriv Xi s = 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s
      + logDeriv riemannZeta s := by
  have hs0 := ne_zero_of_one_lt_re hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
  have hsre : 0 < s.re := by linarith
  have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsre
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hdΓ : DifferentiableAt ℂ Complex.Gammaℝ s :=
    Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ s hsre
  have hdz : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (ne_one_of_one_lt_re hs)
  have hdhead : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s := by fun_prop
  have hhead0 : ((1 / 2 : ℂ) * s * (s - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1
  have hev : Xi =ᶠ[𝓝 s]
      fun z : ℂ => ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ) := by
    filter_upwards [isOpen_re_gt_one.mem_nhds hs] with z hz
    exact Xi_eq_head_mul hz
  have hcongr : logDeriv Xi s
      = logDeriv (fun z : ℂ => ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ)) s :=
    (logDeriv_congr_nhds hev).eq_of_nhds
  rw [hcongr]
  have houter := logDeriv_mul (x := s) (f := fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1))
    (g := fun z : ℂ => riemannZeta z * z.Gammaℝ) hhead0 (mul_ne_zero hz hG) hdhead (hdz.mul hdΓ)
  erw [houter]
  have hinner := logDeriv_mul (x := s) (f := riemannZeta) (g := fun z : ℂ => z.Gammaℝ)
    hz hG hdz hdΓ
  erw [hinner]; rw [logDeriv_head s hs0 hs1]
  ring

/-! ## The completed `L`-function: `Λ_χ = L(·,χ) · (Γ-factor)` -/

lemma gammaFactor_eq_Gammaℝ_or {N : ℕ} (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.gammaFactor χ = Complex.Gammaℝ ∨
      DirichletCharacter.gammaFactor χ = fun z : ℂ => Complex.Gammaℝ (z + 1) := by
  rcases χ.even_or_odd with h | h
  · left; funext z; exact h.gammaFactor_def z
  · right; funext z; exact h.gammaFactor_def z

lemma logDeriv_gammaFactor_of_even {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ.Even)
    (s : ℂ) : logDeriv (DirichletCharacter.gammaFactor χ) s = logDeriv Complex.Gammaℝ s := by
  have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
    funext z; exact h.gammaFactor_def z
  rw [hfun]

lemma logDeriv_gammaFactor_of_odd {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ.Odd)
    (s : ℂ) : logDeriv (DirichletCharacter.gammaFactor χ) s
      = logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s := by
  have hfun : DirichletCharacter.gammaFactor χ = fun z : ℂ => Complex.Gammaℝ (z + 1) := by
    funext z; exact h.gammaFactor_def z
  rw [hfun]

lemma level_ne_one_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    N ≠ 1 := by
  rintro rfl
  exact hχ (DirichletCharacter.level_one' χ rfl)

lemma completedLFunction_eq_L_mul_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hγ : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DirichletCharacter.completedLFunction χ s
      = DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s
    (Or.inr (level_ne_one_of_ne_one hχ))
  rw [h, div_mul_cancel₀ _ hγ]

lemma re_add_one_of_pos {s : ℂ} (hs : 0 < s.re) : 0 < (s + 1).re := by
  simp only [Complex.add_re, Complex.one_re]; linarith

lemma completedLFunction_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s
      = logDeriv (DirichletCharacter.LFunction χ) s
        + logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hsre : 0 < s.re := by linarith
  have hγpos : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases gammaFactor_eq_Gammaℝ_or χ with h | h
    · rw [h]; exact Gammaℝ_ne_zero_of_re_pos hsre
    · rw [h]; exact Gammaℝ_add_one_ne_zero_of_re_pos hsre
  have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  have hdL : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)
  have hdγ : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
    rcases gammaFactor_eq_Gammaℝ_or χ with h | h
    · rw [h]; exact Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ s hsre
    · rw [h]
      have hinner : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
      exact DifferentiableAt.comp s
        (Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ
          (s + 1) (re_add_one_of_pos hsre)) hinner
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      fun z => DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z := by
    filter_upwards [isOpen_re_gt_one.mem_nhds hs] with z hz
    refine completedLFunction_eq_L_mul_gammaFactor χ hχ z ?_
    rcases gammaFactor_eq_Gammaℝ_or χ with h | h
    · rw [h]; exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [h]; exact Gammaℝ_add_one_ne_zero_of_re_pos (by linarith)
  rw [((logDeriv_congr_nhds hev).eq_of_nhds)]
  exact logDeriv_mul _ hL hγpos hdL hdγ

lemma Xi_add_completedL_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    logDeriv Xi s + logDeriv (DirichletCharacter.completedLFunction χ) s
      = (logDeriv riemannZeta s + logDeriv (DirichletCharacter.LFunction χ) s)
        + (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s
            + logDeriv (DirichletCharacter.gammaFactor χ) s) := by
  rw [Xi_logDeriv s hs, completedLFunction_logDeriv χ hχ s hs]
  ring

end

end Work.LinnikAreas.DhK
