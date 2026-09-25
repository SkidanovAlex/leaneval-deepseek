/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Cauchy–Green (Pompeiu) formula at the origin

This file proves `cauchyGreen_origin`: for a `C¹` function `f` on `ℂ` vanishing outside the disc
of radius `R`, `-(1/π) ∫_{‖ζ‖<R} (∂̄f)(ζ)/ζ dA(ζ) = f 0`.

The proof is the polar-coordinate computation: write `ζ = ρ e^{iθ}`, use
`Complex.integral_comp_polarCoord_symm` to push the area integral to
`(0,∞) × (-π,π)`, rewrite the integrand pointwise as
`(1/2)(∂_ρ G + (i/ρ) ∂_θ G)` with `G(ρ,θ) = f(ρ e^{iθ})`, and evaluate the two
iterated integrals by the fundamental theorem of calculus in `θ` and in `ρ`
(using Fubini).
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy

noncomputable section

open scoped NNReal ENNReal Real Topology
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## The unit complex number `e^{iθ}` -/

/-- `e^{i θ}`, as a function of the real variable `θ`. -/
noncomputable def polarUnit (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

lemma polarUnit_apply (θ : ℝ) :
    polarUnit θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [polarUnit, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma norm_polarUnit (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  rw [polarUnit, Complex.norm_exp, Complex.mul_re]; simp

lemma polarUnit_neg (θ : ℝ) : polarUnit (-θ) = (polarUnit θ)⁻¹ := by
  simp only [polarUnit, Complex.ofReal_neg, neg_mul, Complex.exp_neg]

lemma inv_polarUnit (θ : ℝ) :
    (polarUnit θ)⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [← polarUnit_neg, polarUnit_apply]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

lemma hasDerivAt_polarUnit (θ : ℝ) : HasDerivAt polarUnit (polarUnit θ * Complex.I) θ := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I θ := by
    have := (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
    simpa using this
  exact (Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).comp θ h1

lemma polarUnit_mul_I (θ : ℝ) :
    polarUnit θ * Complex.I = -(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * Complex.I := by
  rw [polarUnit, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * polarUnit p.2 := by
  rw [Complex.polarCoord_symm_apply, polarUnit_apply]

lemma polarUnit_pi : polarUnit Real.pi = -1 := by
  rw [polarUnit, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  norm_num [Real.cos_pi, Real.sin_pi]

lemma polarUnit_neg_pi : polarUnit (-Real.pi) = -1 := by
  rw [polarUnit, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Real.cos_pi, Real.sin_pi]

lemma continuous_polarUnit : Continuous polarUnit := by
  rw [show polarUnit = fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) from rfl]
  fun_prop

lemma continuous_polarCoord_symm : Continuous Complex.polarCoord.symm := by
  rw [show Complex.polarCoord.symm = fun p : ℝ × ℝ => (p.1 : ℂ) * polarUnit p.2
      from funext polarCoord_symm_eq]
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    (continuous_polarUnit.comp continuous_snd)

/-- `Complex.polarCoord.symm` at `θ = ±π` gives the same (negative real) point. -/
lemma polarCoord_symm_pi (ρ : ℝ) :
    Complex.polarCoord.symm (ρ, Real.pi) = Complex.polarCoord.symm (ρ, -Real.pi) := by
  rw [polarCoord_symm_eq, polarCoord_symm_eq, polarUnit_pi, polarUnit_neg_pi]

/-! ## The pointwise polar form of the integrand -/

/-- Decomposition of an `ℝ`-linear map `ℂ → ℂ` on the real basis `(1, I)`. -/
lemma apply_real_decomp (F : ℂ →L[ℝ] ℂ) (a b : ℝ) :
    F ((a : ℂ) + (b : ℂ) * Complex.I) = (a : ℂ) * F 1 + (b : ℂ) * F Complex.I := by
  rw [show (a : ℂ) + (b : ℂ) * Complex.I = a • (1 : ℂ) + b • (Complex.I : ℂ) by
        rw [Complex.real_smul, Complex.real_smul]; ring]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- The algebraic kernel of the Cauchy–Green formula:
`F u + i F (i u) = (F 1 + i F i) / u` for `u = e^{iθ}`. -/
lemma polar_algebra (F : ℂ →L[ℝ] ℂ) (θ : ℝ) :
    F (polarUnit θ) + Complex.I * F (polarUnit θ * Complex.I)
      = (F 1 + Complex.I * F Complex.I) * (polarUnit θ)⁻¹ := by
  have h2 : F (polarUnit θ * Complex.I)
      = -(Real.sin θ : ℂ) * F 1 + (Real.cos θ : ℂ) * F Complex.I := by
    rw [polarUnit_mul_I,
      show -(Real.sin θ : ℂ) = (((-(Real.sin θ)) : ℝ) : ℂ) by push_cast; ring]
    exact apply_real_decomp F (-(Real.sin θ)) (Real.cos θ)
  rw [h2, inv_polarUnit, polarUnit_apply, apply_real_decomp F (Real.cos θ) (Real.sin θ)]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `ρ`-direction derivative of `f` in polar coordinates. -/
noncomputable def polA (f : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ f (Complex.polarCoord.symm p) (polarUnit p.2)

/-- `θ`-direction derivative of `f` in polar coordinates, stripped of its factor `ρ`. -/
noncomputable def polD (f : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.I * fderiv ℝ f (Complex.polarCoord.symm p) (polarUnit p.2 * Complex.I)

/-- `θ`-direction derivative of `f` in polar coordinates. -/
noncomputable def polB (f : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ f (Complex.polarCoord.symm p) ((p.1 : ℂ) * (polarUnit p.2 * Complex.I))

/-- The polar form of `ρ • ((∂̄f)(ζ)/ζ)`. -/
noncomputable def polPhi (f : ℂ → ℂ) (p : ℝ × ℝ) : ℂ := (1/2) * (polA f p + polD f p)

lemma polB_eq (f : ℂ → ℂ) (p : ℝ × ℝ) :
    polB f p = (p.1 : ℂ) * fderiv ℝ f (Complex.polarCoord.symm p) (polarUnit p.2 * Complex.I) := by
  rw [polB, ← Complex.real_smul, ContinuousLinearMap.map_smul, Complex.real_smul]

/-- The pointwise identity behind the whole computation. -/
lemma polar_smul_dbar {f : ℂ → ℂ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 • (dbarC f (Complex.polarCoord.symm p) / Complex.polarCoord.symm p) = polPhi f p := by
  have hu : polarUnit p.2 ≠ 0 := by
    intro h; have := norm_polarUnit p.2; rw [h] at this; simp at this
  have hρ : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  rw [polarCoord_symm_eq, dbarC]
  simp only [polPhi, polA, polD, polarCoord_symm_eq]
  rw [polar_algebra (fderiv ℝ f ((p.1 : ℂ) * polarUnit p.2)) p.2]
  rw [Complex.real_smul, div_eq_mul_inv, mul_inv]
  field_simp

/-! ## Chain rule: the two partial derivatives of `G (ρ,θ) = f (ρ e^{iθ})` -/

lemma hasDerivAt_rho {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (p : ℝ × ℝ) :
    HasDerivAt (fun ρ : ℝ => f (Complex.polarCoord.symm (ρ, p.2))) (polA f p) p.1 := by
  have hdiff : HasFDerivAt f (fderiv ℝ f ((p.1 : ℂ) * polarUnit p.2))
      ((p.1 : ℂ) * polarUnit p.2) := by
    rw [← polarCoord_symm_eq]
    exact (hf.differentiable_one.differentiableAt).hasFDerivAt
  have hlin : HasDerivAt (fun ρ : ℝ => (ρ : ℂ) * polarUnit p.2) (polarUnit p.2) p.1 := by
    simpa using (hasDerivAt_id p.1).ofReal_comp.mul_const (polarUnit p.2)
  have hcomp := hdiff.comp_hasDerivAt p.1 hlin
  simpa only [Function.comp_def, polarCoord_symm_eq, polA] using hcomp

lemma hasDerivAt_theta {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (p : ℝ × ℝ) :
    HasDerivAt (fun θ : ℝ => f (Complex.polarCoord.symm (p.1, θ))) (polB f p) p.2 := by
  have hdiff : HasFDerivAt f (fderiv ℝ f ((p.1 : ℂ) * polarUnit p.2))
      ((p.1 : ℂ) * polarUnit p.2) := by
    rw [← polarCoord_symm_eq]
    exact (hf.differentiable_one.differentiableAt).hasFDerivAt
  have hlin : HasDerivAt (fun θ : ℝ => (p.1 : ℂ) * polarUnit θ)
      ((p.1 : ℂ) * (polarUnit p.2 * Complex.I)) p.2 :=
    (hasDerivAt_polarUnit p.2).const_mul (p.1 : ℂ)
  have hcomp := hdiff.comp_hasDerivAt p.2 hlin
  simpa only [Function.comp_def, polarCoord_symm_eq, polB] using hcomp

/-! ## Continuity and integrability -/

lemma continuous_polA {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (polA f) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f (Complex.polarCoord.symm p)) :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_polarCoord_symm
  have h2 : Continuous (fun p : ℝ × ℝ => polarUnit p.2) := continuous_polarUnit.comp continuous_snd
  exact h1.clm_apply h2

lemma continuous_polD {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (polD f) := by
  have ha : Continuous (fun p : ℝ × ℝ => fderiv ℝ f (Complex.polarCoord.symm p)) :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_polarCoord_symm
  have hb : Continuous (fun p : ℝ × ℝ => polarUnit p.2 * Complex.I) :=
    (continuous_polarUnit.comp continuous_snd).mul continuous_const
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f (Complex.polarCoord.symm p)
      (polarUnit p.2 * Complex.I)) := ha.clm_apply hb
  rw [show polD f = fun p : ℝ × ℝ => Complex.I * fderiv ℝ f (Complex.polarCoord.symm p)
      (polarUnit p.2 * Complex.I) from rfl]
  exact continuous_const.mul h1

lemma continuous_polB {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (polB f) := by
  have ha : Continuous (fun p : ℝ × ℝ => fderiv ℝ f (Complex.polarCoord.symm p)) :=
    (hf.continuous_fderiv one_ne_zero).comp continuous_polarCoord_symm
  have hb : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (polarUnit p.2 * Complex.I)) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      ((continuous_polarUnit.comp continuous_snd).mul continuous_const)
  exact ha.clm_apply hb

/-- A continuous function on a product of open intervals is integrable there. -/
lemma integrableOn_Ioo_prod_of_continuous {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    (a b c d : ℝ) : IntegrableOn F (Ioo a b ×ˢ Ioo c d) (volume : Measure (ℝ × ℝ)) := by
  have hK : IsCompact (Icc a b ×ˢ Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  exact (ContinuousOn.integrableOn_compact hK hF.continuousOn).mono_set
    (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- Fubini for set integrals in the "reversed" order. -/
lemma setIntegral_prod_rev {F : ℝ × ℝ → ℂ} {s t : Set ℝ}
    (h : IntegrableOn (fun z : ℝ × ℝ => F z.swap) (t ×ˢ s) (volume.prod volume)) :
    ∫ p in s ×ˢ t, F p ∂(volume.prod volume) = ∫ y in t, ∫ x in s, F (x, y) := by
  rw [← setIntegral_prod_swap s t F]
  exact setIntegral_prod (s := t) (t := s) (fun z : ℝ × ℝ => F z.swap) h

/-! ## The two fundamental-theorem-of-calculus steps -/

lemma integral_deriv_rho {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R)
    (hfsupp : SupportedInBall R f) (θ : ℝ) :
    ∫ ρ in (0)..R, polA f (ρ, θ) = -(f 0) := by
  have hderiv : ∀ ρ ∈ uIcc (0 : ℝ) R,
      HasDerivAt (fun ρ : ℝ => f (Complex.polarCoord.symm (ρ, θ))) (polA f (ρ, θ)) ρ :=
    fun ρ _ => hasDerivAt_rho hf (ρ, θ)
  have hcont : Continuous (fun ρ : ℝ => polA f (ρ, θ)) :=
    (continuous_polA hf).comp (continuous_id.prodMk continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 R)]
  have h1 : f (Complex.polarCoord.symm (R, θ)) = 0 := by
    apply hfsupp
    simp [Complex.norm_polarCoord_symm, abs_of_pos hR]
  have h2 : Complex.polarCoord.symm (0, θ) = 0 := by
    rw [polarCoord_symm_eq]; simp
  rw [h1, h2]
  ring

lemma integral_deriv_theta {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (ρ : ℝ) :
    ∫ θ in (-Real.pi)..Real.pi, polB f (ρ, θ) = 0 := by
  have hderiv : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
      HasDerivAt (fun θ : ℝ => f (Complex.polarCoord.symm (ρ, θ))) (polB f (ρ, θ)) θ :=
    fun θ _ => hasDerivAt_theta hf (ρ, θ)
  have hcont : Continuous (fun θ : ℝ => polB f (ρ, θ)) :=
    (continuous_polB hf).comp (continuous_const.prodMk continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  rw [polarCoord_symm_pi ρ]
  ring

/-! ## The main theorem -/

/-- **Pompeiu/Cauchy–Green formula at the origin**: for `C¹` `f` vanishing off the disc of radius
`R`, `-(1/π) ∫_{‖ζ‖<R} (∂̄f)(ζ)/ζ dA(ζ) = f 0`.  (The integrand is supported in `‖ζ‖ ≤ R`.)

Suggested route, all in polar coordinates (`Complex.polarCoord`,
`Complex.integral_comp_polarCoord_symm`, `Complex.polarCoord_target`,
`Complex.polarCoord_symm_apply`, `Complex.norm_polarCoord_symm`): with
`G (ρ,θ) = f (Complex.polarCoord.symm (ρ,θ))` one has `G (ρ,θ) = 0` for `ρ ≥ R`,
`G (0,θ) = f 0` and
`∫_ℂ (∂̄f)(ζ)/ζ = ∫ p in Complex.polarCoord.target, p.1 • ((∂̄f)(Complex.polarCoord.symm p)/(Complex.polarCoord.symm p))`,
whose integrand is `(1/2) * (fderiv ℝ G p (1,0) + (I/p.1) * fderiv ℝ G p (0,1))`
(chain rule; `fderiv ℝ f` is only ℝ-linear).  Then
`∫_{θ ∈ (-π,π)} ∂_θ G dθ = G(ρ,π) - G(ρ,-π) = 0` (as `polarCoord.symm (ρ,π) = polarCoord.symm (ρ,-π) = -ρ`)
and `∫_{ρ ∈ (0,∞)} ∂_ρ G dρ = -f 0`, giving `-π f 0`.  Use
`intervalIntegral.integral_eq_sub_of_hasDerivAt` and Fubini
(`MeasureTheory.integral_integral_swap`, `MeasureTheory.Measure.volume_eq_prod`). -/
theorem cauchyGreen_origin {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall R f) :
    -((Real.pi : ℂ))⁻¹ * ∫ ζ in Metric.ball (0 : ℂ) R, (Work.CR.Flat.dbarC f ζ) / ζ = f 0 := by
  set U : Set (ℝ × ℝ) := Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi with hU
  -- integrability of the pieces
  have hIntA : IntegrableOn (polA f) U (volume : Measure (ℝ × ℝ)) := by
    rw [hU]
    exact integrableOn_Ioo_prod_of_continuous (continuous_polA hf) 0 R (-Real.pi) Real.pi
  have hIntD : IntegrableOn (polD f) U (volume : Measure (ℝ × ℝ)) := by
    rw [hU]
    exact integrableOn_Ioo_prod_of_continuous (continuous_polD hf) 0 R (-Real.pi) Real.pi
  have hIntASwap : IntegrableOn (fun z : ℝ × ℝ => polA f z.swap)
      (Ioo (-Real.pi) Real.pi ×ˢ Ioo (0 : ℝ) R) (volume.prod volume : Measure (ℝ × ℝ)) := by
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact integrableOn_Ioo_prod_of_continuous ((continuous_polA hf).comp continuous_swap)
      (-Real.pi) Real.pi 0 R
  have hIntDprod : IntegrableOn (polD f) U (volume.prod volume : Measure (ℝ × ℝ)) := by
    rw [← Measure.volume_eq_prod ℝ ℝ]; exact hIntD
  -- Step 1: push the integral to polar coordinates
  have hA : ∫ ζ in Metric.ball (0 : ℂ) R, (dbarC f ζ) / ζ = ∫ p in U, polPhi f p := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    rw [(Complex.integral_comp_polarCoord_symm
      ((Metric.ball (0 : ℂ) R).indicator (fun ζ : ℂ => (dbarC f ζ) / ζ))).symm]
    rw [polarCoord_target, hU]
    have key : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (Metric.ball (0 : ℂ) R).indicator (fun ζ : ℂ => (dbarC f ζ) / ζ)
            (Complex.polarCoord.symm p)
          = (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi).indicator (polPhi f) p := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      by_cases hlt : p.1 < R
      · have hmb : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp1]
          exact hlt
        have hmU : p ∈ Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := ⟨⟨hp1, hlt⟩, hp2⟩
        rw [Set.indicator_of_mem hmb, Set.indicator_of_mem hmU]
        exact polar_smul_dbar hp1
      · have hmb : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) R := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp1]
          exact hlt
        have hmU : p ∉ Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := fun h => hlt h.1.2
        rw [Set.indicator_of_notMem hmb, Set.indicator_of_notMem hmU, smul_zero]
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key]
    rw [setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    have hset : (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩
          (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi)
        = Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
      rw [Set.prod_inter_prod, Set.inter_self]
      congr 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_inter_iff]
      tauto
    rw [hset]
  -- Step 2: evaluate the two pieces
  have hA_int : ∫ p in U, polA f p = -(2 * (Real.pi : ℂ)) * f 0 := by
    rw [hU, Measure.volume_eq_prod ℝ ℝ]
    rw [setIntegral_prod_rev (s := Ioo (0 : ℝ) R) (t := Ioo (-Real.pi) Real.pi) hIntASwap]
    have hinner : ∀ θ : ℝ, ∫ ρ in Ioo (0 : ℝ) R, polA f (ρ, θ) = -(f 0) := by
      intro θ
      rw [setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc' Real.volume_singleton)]
      rw [← intervalIntegral.integral_of_le hR.le]
      exact integral_deriv_rho hf hR hfsupp θ
    rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hinner θ)]
    rw [setIntegral_const]
    have hvol : (volume : Measure ℝ).real (Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
      rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [hvol, Complex.real_smul]
    push_cast
    ring
  have hD_int : ∫ p in U, polD f p = 0 := by
    rw [hU, Measure.volume_eq_prod ℝ ℝ]
    rw [setIntegral_prod (polD f) hIntDprod]
    have hinner2 : ∀ ρ : ℝ, 0 < ρ → ∫ θ in Ioo (-Real.pi) Real.pi, polD f (ρ, θ) = 0 := by
      intro ρ hρ
      have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
      have hpoint : ∀ θ : ℝ, polD f (ρ, θ) = (Complex.I / (ρ : ℂ)) * polB f (ρ, θ) := by
        intro θ
        simp only [polD, polB_eq]
        field_simp
      rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hpoint θ)]
      rw [MeasureTheory.integral_const_mul]
      have htheta : ∫ θ in Ioo (-Real.pi) Real.pi, polB f (ρ, θ) = 0 := by
        rw [setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc' Real.volume_singleton)]
        rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        exact integral_deriv_theta hf ρ
      rw [htheta, mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun ρ hρ => hinner2 ρ hρ.1)]
    simp
  have hB : ∫ p in U, polPhi f p = -((Real.pi : ℂ)) * f 0 := by
    have h1 : ∫ p in U, polPhi f p
        = (1 / 2) * ((∫ p in U, polA f p) + (∫ p in U, polD f p)) := by
      simp only [polPhi]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hIntA hIntD]
    rw [h1, hA_int, hD_int]
    ring
  rw [hA, hB]
  rw [← mul_assoc, neg_mul_neg,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

end Work.CR.Flat.Cauchy
