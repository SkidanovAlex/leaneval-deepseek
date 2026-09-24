import Mathlib

namespace Work.SimplyConnected.ABS

set_option linter.unusedVariables false

/-- The real part of `Complex.sqrt w` is the (real) square root of `(‖w‖ + w.re)/2`; this is the
manifestly continuous expression for `(Complex.sqrt w).re`. -/
private lemma sqrt_re_eq (w : ℂ) : (Complex.sqrt w).re = Real.sqrt ((‖w‖ + w.re)/2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [Complex.mul_I_re]
  split_ifs <;> simp

/-- `‖w‖ + w.re` is positive exactly when `w` is neither `0` nor a non-positive real number. -/
private lemma norm_add_re_pos (w : ℂ) : 0 < ‖w‖ + w.re ↔ w.im ≠ 0 ∨ 0 < w.re := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨him, hre⟩ := hc
    have hnorm : ‖w‖ = |w.re| := ((Complex.abs_re_eq_norm (z := w)).2 him).symm
    rw [hnorm, abs_of_nonpos hre] at h
    linarith
  · rintro (him | hre)
    · have hlt : |w.re| < ‖w‖ := Complex.abs_re_lt_norm.2 him
      have := neg_le_abs w.re
      have := abs_nonneg w.re
      linarith
    · have := norm_nonneg w
      linarith

/-- If `-(p⁻¹) * z` is a non-positive real number and `p` lies in the open sector, then `z`
lies in the closed sector `{0 ≤ L₁ z ∧ 0 ≤ L₂ z}`. -/
private lemma sector_mem {L₁ L₂ : ℂ →L[ℝ] ℝ} {p z : ℂ} (hp : p ≠ 0)
    (hp₁ : 0 < L₁ p) (hp₂ : 0 < L₂ p)
    (him : (-(p⁻¹) * z).im = 0) (hre : (-(p⁻¹) * z).re ≤ 0) :
    0 ≤ L₁ z ∧ 0 ≤ L₂ z := by
  set t : ℝ := -(-(p⁻¹) * z).re with htdef
  have ht : 0 ≤ t := by rw [htdef]; linarith
  have hw_re : -(p⁻¹) * z = ((-(p⁻¹) * z).re : ℂ) := by
    have h := Complex.re_add_im (-(p⁻¹) * z)
    rw [him] at h
    simpa using h.symm
  have hw_eq : -(p⁻¹) * z = -(t : ℂ) := by
    rw [hw_re, htdef]; push_cast; ring
  have h2 : p⁻¹ * z = (t : ℂ) := by
    have := congrArg Neg.neg hw_eq
    simpa using this
  have hz_eq : z = (t : ℂ) * p := by
    calc z = p * (p⁻¹ * z) := by rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
      _ = p * (t : ℂ) := by rw [h2]
      _ = (t : ℂ) * p := by ring
  have hL₁ : L₁ z = t * L₁ p := by
    have hz' : z = t • p := hz_eq
    rw [hz', L₁.map_smul, smul_eq_mul]
  have hL₂ : L₂ z = t * L₂ p := by
    have hz' : z = t • p := hz_eq
    rw [hz', L₂.map_smul, smul_eq_mul]
  exact ⟨by rw [hL₁]; exact mul_nonneg ht (le_of_lt hp₁),
         by rw [hL₂]; exact mul_nonneg ht (le_of_lt hp₂)⟩

/-- **The plane sector barrier (continuous form).**  Let `L₁ L₂ : ℂ →L[ℝ] ℝ` be non-zero real-linear functionals whose sector `{w | 0 < L₁ w ∧ 0 < L₂ w}` is non-empty.  Then there is a function `φ : ℂ → ℝ`, continuous on all of `ℂ`, vanishing at the origin, harmonic off the apex on the complement of the closed sector `{w | 0 ≤ L₁ w ∧ 0 ≤ L₂ w}`, and strictly positive on that complement. -/
theorem plane_sector_barrier_continuous (L₁ L₂ : ℂ →L[ℝ] ℝ) (h₁ : L₁ ≠ 0) (h₂ : L₂ ≠ 0)
    (hne : ∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) :
    ∃ φ : ℂ → ℝ, Continuous φ ∧ φ 0 = 0 ∧
      (∀ z : ℂ, ¬ (0 ≤ L₁ z ∧ 0 ≤ L₂ z) → 0 < φ z) ∧
      (∀ z : ℂ, ¬ (0 ≤ L₁ z ∧ 0 ≤ L₂ z) → InnerProductSpace.HarmonicAt φ z) := by
  -- Pick a point `p` of the open sector; the barrier is `Re (sqrt (-z/p))`, whose branch cut is
  -- the ray through `p`, contained in the closed sector.
  obtain ⟨p, hp₁, hp₂⟩ := hne
  have hp : p ≠ 0 := by
    intro h; rw [h] at hp₁; simp at hp₁
  refine ⟨fun z => (Complex.sqrt (-(p⁻¹) * z)).re, ?_, ?_, ?_, ?_⟩
  · -- continuity, through the explicit real expression for the real part of the square root
    have hfun : (fun z : ℂ => (Complex.sqrt (-(p⁻¹) * z)).re)
        = fun z : ℂ => Real.sqrt ((‖-(p⁻¹) * z‖ + (-(p⁻¹) * z).re)/2) := by
      funext z; exact sqrt_re_eq _
    rw [hfun]; fun_prop
  · -- vanishing at the apex
    simp
  · -- strict positivity off the closed sector
    intro z hz
    have hgt : 0 < ‖-(p⁻¹) * z‖ + (-(p⁻¹) * z).re := by
      rw [norm_add_re_pos]
      by_contra hc
      push Not at hc
      exact hz (sector_mem hp hp₁ hp₂ hc.1 hc.2)
    change 0 < (Complex.sqrt (-(p⁻¹) * z)).re
    rw [sqrt_re_eq]
    exact Real.sqrt_pos.2 (by linarith)
  · -- harmonicity off the branch cut, which lies inside the closed sector
    intro z hz
    have hw : -(p⁻¹) * z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hc
      push Not at hc
      exact hz (sector_mem hp hp₁ hp₂ hc.2 hc.1)
    have hana : AnalyticAt ℂ Complex.sqrt (-(p⁻¹) * z) :=
      Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hw)
    have hcomp : AnalyticAt ℂ (Complex.sqrt ∘ (⇑(-(p⁻¹) • (1 : ℂ →L[ℂ] ℂ)))) z :=
      hana.compContinuousLinearMap
    exact hcomp.harmonicAt_re

end Work.SimplyConnected.ABS
