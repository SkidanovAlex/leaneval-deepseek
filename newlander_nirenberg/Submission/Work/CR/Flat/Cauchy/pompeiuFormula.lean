import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal Topology
open MeasureTheory Set Complex Filter

/-!
# Pompeiu's formula (Cauchy–Green) on the plane

We prove `Work.CR.Flat.Cauchy.pompeiuFormula`: for a `C¹` function `f` vanishing outside the disc
of radius `R` and `‖z‖ < R`, `-(1/π) ∫_{‖ζ‖<R} (∂̄f)(ζ)/(ζ-z) dA(ζ) = f z`.

The proof is by polar coordinates: after reducing to the origin, the integral becomes
`∫ p in (0,∞)×(-π,π), p.1 • ((∂̄f)(polarCoord.symm p)/polarCoord.symm p)`, the integrand is
`(1/2)(∂_ρ G + (I/ρ) ∂_θ G)` with `G = f ∘ polarCoord.symm`, the angular part integrates to `0`
and the radial part to `-2π f 0`.

The file collects the purely algebraic identity, the one-variable fundamental theorem of calculus
computations in `ρ` and `θ`, and finally assembles them via Fubini.
-/

/-! ## Auxiliary algebra of the polar-coordinate computation -/

/-- A real-linear map `ℂ → ℂ` is determined by its values on the real basis `1, I` of `ℂ`. -/
lemma pompeiu_clm_expand (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = (z.re : ℂ) * L 1 + (z.im : ℂ) * L I := by
  have h : z = z.re • (1:ℂ) + z.im • (I:ℂ) := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul]
  rfl

/-- The elementary algebraic identity behind the polar-coordinate form of `∂̄`. -/
lemma pompeiu_complex_polar_alg (a b : ℂ) (c s ρ : ℝ) (hρ : ρ ≠ 0) :
    (c:ℂ)*a + (s:ℂ)*b + (Complex.I/ρ)*((-(ρ*s):ℂ)*a + (ρ*c:ℂ)*b)
      = ((c:ℂ) - (s:ℂ)*Complex.I)*(a + Complex.I*b) := by
  have hρ' : (ρ:ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp
  ring_nf
  rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
  ring

lemma pompeiu_I_mul_re (ρ θ : ℝ) :
    (Complex.I * ((ρ:ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))).re
      = -(ρ*Real.sin θ) := by
  rw [show Complex.I * ((ρ:ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))
      = (-(ρ*Real.sin θ):ℂ) + (ρ*Real.cos θ : ℂ)*Complex.I by
    ring_nf
    rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_im]
  ring

lemma pompeiu_I_mul_im (ρ θ : ℝ) :
    (Complex.I * ((ρ:ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))).im
      = ρ*Real.cos θ := by
  rw [show Complex.I * ((ρ:ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))
      = (-(ρ*Real.sin θ):ℂ) + (ρ*Real.cos θ : ℂ)*Complex.I by
    ring_nf
    rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re]
  ring

lemma pompeiu_polar_algebra (L : ℂ →L[ℝ] ℂ) (ρ θ : ℝ) (hρ : 0 < ρ) :
    L ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)
      + (Complex.I / (ρ:ℂ)) * L (Complex.I * ((ρ:ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)))
    = ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) * (L 1 + Complex.I * L Complex.I) := by
  have h1re : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I).re = Real.cos θ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have h1im : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I).im = Real.sin θ := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]
  rw [pompeiu_clm_expand L ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I),
      pompeiu_clm_expand L (Complex.I * ((ρ:ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))),
      h1re, h1im, pompeiu_I_mul_re, pompeiu_I_mul_im]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  exact pompeiu_complex_polar_alg (L 1) (L Complex.I) (Real.cos θ) (Real.sin θ) ρ (ne_of_gt hρ)

lemma pompeiu_cis_inv (c s : ℝ) (h : c^2 + s^2 = 1) :
    ((c:ℂ) + (s:ℂ)*Complex.I)⁻¹ = (c:ℂ) - (s:ℂ)*Complex.I := by
  have h1 : ((c:ℂ) + (s:ℂ)*Complex.I) * ((c:ℂ) - (s:ℂ)*Complex.I) = 1 := by
    have : ((c:ℂ) + (s:ℂ)*Complex.I) * ((c:ℂ) - (s:ℂ)*Complex.I) = (c:ℂ)^2 + (s:ℂ)^2 := by
      ring_nf
      rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
      ring
    rw [this, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, h]
    norm_num
  exact inv_eq_of_mul_eq_one_right h1

lemma pompeiu_polar_rho_div (ρ θ : ℝ) (hρ : 0 < ρ) :
    (ρ:ℂ)/((ρ:ℂ)*((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I))
      = (Real.cos θ:ℂ) - (Real.sin θ:ℂ)*Complex.I := by
  have hρ' : (ρ:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hρ', one_mul]
  exact pompeiu_cis_inv (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ)

lemma pompeiu_final_alg (y : ℂ) (ρ θ : ℝ) (hρ : 0 < ρ) :
    2 * ((ρ:ℂ) * ((1/2) * y / ((ρ:ℂ)*((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I))))
      = ((Real.cos θ:ℂ) - (Real.sin θ:ℂ)*Complex.I) * y := by
  have h1 : (ρ:ℂ) * ((1/2)*y / ((ρ:ℂ)*((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I)))
      = ((ρ:ℂ)/((ρ:ℂ)*((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I))) * ((1/2)*y) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [h1, pompeiu_polar_rho_div ρ θ hρ]
  ring

/-! ## The polar coordinate map -/

/-- `p ↦ Complex.polarCoord.symm p` is `C¹`. -/
lemma pompeiu_contDiff_polar_symm :
    ContDiff ℝ 1 (fun p : ℝ×ℝ => (Complex.polarCoord.symm p : ℂ)) := by
  simp only [Complex.polarCoord_symm_apply]
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp contDiff_fst
  · apply ContDiff.add
    · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_snd)
    · apply ContDiff.mul
      · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)
      · exact contDiff_const

/-- The two directional derivatives of `G = f ∘ Complex.polarCoord.symm`. -/
lemma pompeiu_fderiv_polarG_apply {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (p : ℝ×ℝ) :
    fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0)
        = fderiv ℝ f (Complex.polarCoord.symm p)
            ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ)*Complex.I)
    ∧ fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1)
        = fderiv ℝ f (Complex.polarCoord.symm p) (Complex.I * Complex.polarCoord.symm p) := by
  have hcc : HasFDerivAt (fun q : ℝ×ℝ => (Complex.polarCoord.symm q : ℂ))
      (((Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ)).comp (fderivPolarCoordSymm p)) p := by
    have h1 : HasFDerivAt (fun q : ℝ×ℝ => polarCoord.symm q) (fderivPolarCoordSymm p) p :=
      hasFDerivAt_polarCoord_symm p
    have h2 : HasFDerivAt (fun x : ℝ×ℝ => (Complex.equivRealProdCLM.symm x : ℂ))
        (Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ) (polarCoord.symm p) :=
      (Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ).hasFDerivAt
    have h3 := HasFDerivAt.comp (f := fun q : ℝ×ℝ => polarCoord.symm q)
      (g := fun x : ℝ×ℝ => (Complex.equivRealProdCLM.symm x : ℂ)) p h2 h1
    convert h3 using 1
    ext q
    simp only [Complex.polarCoord_symm_apply, Complex.equivRealProdCLM_symm_apply, polarCoord_symm_apply,
      Complex.ofReal_mul, Function.comp_apply]
    ring
  have hf' : HasFDerivAt f (fderiv ℝ f (Complex.polarCoord.symm p)) (Complex.polarCoord.symm p) :=
    (hf.differentiable one_ne_zero _).hasFDerivAt
  have hGf : fderiv ℝ (fun q : ℝ × ℝ => f (Complex.polarCoord.symm q)) p
      = (fderiv ℝ f (Complex.polarCoord.symm p)).comp
          (((Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ)).comp (fderivPolarCoordSymm p)) :=
    (hf'.comp p hcc).fderiv
  have ee1 : (Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ) (fderivPolarCoordSymm p (1, 0))
      = (Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I := by
    rw [show fderivPolarCoordSymm p (1, 0) = (Real.cos p.2, Real.sin p.2) by
      simp only [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap]; simp]
    rw [show ((Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ)) (Real.cos p.2, Real.sin p.2)
        = Complex.equivRealProdCLM.symm (Real.cos p.2, Real.sin p.2) from rfl]
    rw [Complex.equivRealProdCLM_symm_apply]
  have ee2 : (Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ) (fderivPolarCoordSymm p (0, 1))
      = Complex.I * Complex.polarCoord.symm p := by
    rw [show fderivPolarCoordSymm p (0, 1) = (-(p.1 * Real.sin p.2), p.1 * Real.cos p.2) by
      simp only [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap]; simp]
    rw [show ((Complex.equivRealProdCLM.symm : ℝ×ℝ →L[ℝ] ℂ)) (-(p.1 * Real.sin p.2), p.1 * Real.cos p.2)
        = Complex.equivRealProdCLM.symm (-(p.1 * Real.sin p.2), p.1 * Real.cos p.2) from rfl]
    rw [Complex.equivRealProdCLM_symm_apply, Complex.polarCoord_symm_apply]
    push_cast
    ring_nf
    rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring
  constructor
  · rw [hGf]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ee1]
  · rw [hGf]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ee2]

/-- **Pointwise chain-rule identity for the polar-coordinate form of `∂̄`.** -/
lemma pompeiu_polar_dbar_identity {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (p : ℝ × ℝ) (hp : 0 < p.1) :
    fderiv ℝ (fun q : ℝ × ℝ => f (Complex.polarCoord.symm q)) p (1, 0)
      + (Complex.I / (p.1 : ℂ))
        * fderiv ℝ (fun q : ℝ × ℝ => f (Complex.polarCoord.symm q)) p (0, 1)
    = 2 * ((p.1 : ℂ) * (Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)
        / Complex.polarCoord.symm p)) := by
  have e1 := (pompeiu_fderiv_polarG_apply hf p).1
  have e2 := (pompeiu_fderiv_polarG_apply hf p).2
  have hζ : Complex.polarCoord.symm p
      = (p.1:ℂ)*((Real.cos p.2:ℂ)+(Real.sin p.2:ℂ)*Complex.I) := by
    rw [Complex.polarCoord_symm_apply]
  rw [e1, e2, hζ]
  rw [pompeiu_polar_algebra (fderiv ℝ f ((p.1:ℂ)*((Real.cos p.2:ℂ)+(Real.sin p.2:ℂ)*Complex.I)))
        p.1 p.2 hp]
  have hdb : Work.CR.Flat.dbarC f ((p.1:ℂ)*((Real.cos p.2:ℂ)+(Real.sin p.2:ℂ)*Complex.I))
      = (1/2) * ((fderiv ℝ f ((p.1:ℂ)*((Real.cos p.2:ℂ)+(Real.sin p.2:ℂ)*Complex.I))) 1
          + Complex.I
            * (fderiv ℝ f ((p.1:ℂ)*((Real.cos p.2:ℂ)+(Real.sin p.2:ℂ)*Complex.I))) Complex.I) := by
    rw [Work.CR.Flat.dbarC]
  rw [hdb]
  exact (pompeiu_final_alg _ p.1 p.2 hp).symm

/-! ## The one-variable FTC computations -/

lemma pompeiu_hasDerivAt_radial {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (ρ θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (Complex.polarCoord.symm (t, θ)))
      (fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) (ρ,θ) (1,0)) ρ := by
  have hG : HasFDerivAt (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q))
      (fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) (ρ,θ)) (ρ,θ) :=
    ((hf.comp pompeiu_contDiff_polar_symm).differentiable one_ne_zero (ρ,θ)).hasFDerivAt
  have hφ : HasDerivAt (fun t : ℝ => (t, θ)) (1,0) ρ := by
    have h := (hasFDerivAt_prodMk_left (𝕜 := ℝ) ρ θ).hasDerivAt
    simpa using h
  have := hG.comp_hasDerivAt ρ hφ
  simpa [Function.comp_def] using this

lemma pompeiu_hasDerivAt_angular {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (ρ θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (Complex.polarCoord.symm (ρ, t)))
      (fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) (ρ,θ) (0,1)) θ := by
  have hG : HasFDerivAt (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q))
      (fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) (ρ,θ)) (ρ,θ) :=
    ((hf.comp pompeiu_contDiff_polar_symm).differentiable one_ne_zero (ρ,θ)).hasFDerivAt
  have hφ : HasDerivAt (fun t : ℝ => (ρ, t)) (0,1) θ := by
    have h := (hasFDerivAt_prodMk_right (𝕜 := ℝ) ρ θ).hasDerivAt
    simpa using h
  have := hG.comp_hasDerivAt θ hφ
  simpa [Function.comp_def] using this

/-- The angular integral of `∂_θ G` vanishes (the two endpoints of `θ` give the same point). -/
lemma pompeiu_polar_angular_integral {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (ρ : ℝ) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) (ρ,θ) (0,1) = 0 := by
  set G : ℝ×ℝ → ℂ := fun q => f (Complex.polarCoord.symm q) with hGdef
  have hGc : Continuous G := (hf.comp pompeiu_contDiff_polar_symm).continuous
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (x := -Real.pi) (y := Real.pi),
      ← intervalIntegral.integral_of_le hpi]
  have hcont : ContinuousOn (fun t : ℝ => G (ρ, t)) (Icc (-Real.pi) Real.pi) :=
    (hGc.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hderiv : ∀ x ∈ Ioo (-Real.pi) Real.pi, HasDerivAt (fun t : ℝ => G (ρ,t))
      (fderiv ℝ G (ρ,x) (0,1)) x := by
    intro x hx
    exact pompeiu_hasDerivAt_angular hf ρ x
  have hcont' : Continuous (fun x : ℝ => fderiv ℝ G (ρ,x) (0,1)) := by
    have h1 : Continuous (fun x : ℝ => fderiv ℝ G (ρ,x)) :=
      (((hf.comp pompeiu_contDiff_polar_symm).continuous_fderiv one_ne_zero).comp
        (continuous_const.prodMk continuous_id))
    exact h1.clm_apply continuous_const
  have hint : IntervalIntegrable (fun x : ℝ => fderiv ℝ G (ρ,x) (0,1)) volume (-Real.pi) Real.pi :=
    hcont'.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpi hcont hderiv hint]
  have hcc : Complex.polarCoord.symm (ρ, Real.pi) = Complex.polarCoord.symm (ρ, -Real.pi) := by
    rw [Complex.polarCoord_symm_apply, Complex.polarCoord_symm_apply]
    simp [Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg]
  change f (Complex.polarCoord.symm (ρ, Real.pi)) - f (Complex.polarCoord.symm (ρ, -Real.pi)) = 0
  rw [hcc, sub_self]

/-- The radial integral of `∂_ρ G` equals `-f 0`. -/
lemma pompeiu_polar_radial_integral {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall R f) (θ : ℝ) :
    ∫ ρ in Set.Ioi 0, fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) (ρ,θ) (1,0)
      = - f 0 := by
  set G : ℝ×ℝ → ℂ := fun q => f (Complex.polarCoord.symm q) with hGdef
  have hGc : Continuous G := (hf.comp pompeiu_contDiff_polar_symm).continuous
  have hcont : Continuous (fun ρ : ℝ => G (ρ,θ)) := hGc.comp (continuous_id.prodMk continuous_const)
  have hcont' : Continuous (fun ρ : ℝ => fderiv ℝ G (ρ,θ) (1,0)) := by
    have h1 : Continuous (fun ρ : ℝ => fderiv ℝ G (ρ,θ)) :=
      (((hf.comp pompeiu_contDiff_polar_symm).continuous_fderiv one_ne_zero).comp
        (continuous_id.prodMk continuous_const))
    exact h1.clm_apply continuous_const
  have hGzero : ∀ q : ℝ×ℝ, R ≤ |q.1| → G q = 0 := by
    intro q hq
    change f (Complex.polarCoord.symm q) = 0
    apply hfsupp
    rw [Complex.norm_polarCoord_symm]; exact hq
  have hzero : ∀ ρ : ℝ, R ≤ ρ → G (ρ,θ) = 0 := by
    intro ρ hρ
    exact hGzero (ρ,θ) (by rw [abs_of_nonneg (le_trans hR.le hρ)]; exact hρ)
  have hzero' : ∀ ρ : ℝ, R < ρ → fderiv ℝ G (ρ,θ) (1,0) = 0 := by
    intro ρ hρ
    have hopen : G =ᶠ[𝓝 (ρ,θ)] (fun _ => (0:ℂ)) := by
      apply Filter.mem_of_superset
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds
          (show (ρ,θ) ∈ Ioi R ×ˢ univ from ⟨hρ, mem_univ θ⟩))
      intro q hq
      exact hGzero q (by rw [abs_of_pos (lt_trans hR hq.1)]; exact le_of_lt hq.1)
    rw [hopen.fderiv_eq, fderiv_const_apply]
    simp
  have hint : IntegrableOn (fun ρ : ℝ => fderiv ℝ G (ρ,θ) (1,0)) (Ioi 0) := by
    rw [show Ioi (0:ℝ) = Ioc 0 R ∪ Ioi R by
      ext x; simp only [mem_Ioi, mem_Ioc, mem_union]; constructor
      · intro h
        by_cases hx : x ≤ R
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr (not_le.mp hx)
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · exact lt_trans hR h2]
    rw [integrableOn_union]
    refine ⟨?_, ?_⟩
    · exact (hcont'.integrableOn_Icc (a := 0) (b := R)).mono_set Ioc_subset_Icc_self
    · exact (integrableOn_zero (s := Ioi R)).congr_fun
        (fun x hx => (hzero' x hx).symm) measurableSet_Ioi
  have hev : (fun _ : ℝ => (0:ℂ)) =ᶠ[atTop] (fun ρ => G (ρ,θ)) := by
    filter_upwards [Ici_mem_atTop R] with ρ hρ
    exact (hzero ρ hρ).symm
  have htend : Tendsto (fun ρ : ℝ => G (ρ,θ)) atTop (𝓝 0) :=
    Filter.Tendsto.congr' hev tendsto_const_nhds
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun t : ℝ => G (t,θ))
      (fderiv ℝ G (x,θ) (1,0)) x := by
    intro x hx
    exact pompeiu_hasDerivAt_radial hf x θ
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun ρ => G (ρ,θ))
    (f' := fun ρ => fderiv ℝ G (ρ,θ) (1,0)) (a := 0) (m := 0)
    (hcont.continuousWithinAt) hderiv hint htend
  rw [hmain]
  have h0 : G (0,θ) = f 0 := by
    change f (Complex.polarCoord.symm (0,θ)) = f 0
    congr 1
    rw [Complex.polarCoord_symm_apply]; simp
  rw [h0]
  ring


/-! ## Vanishing of `∂̄f` outside the disc -/

lemma pompeiu_dbarC_eq_zero_of_lt {R : ℝ} {f : ℂ → ℂ}
    (hfsupp : Work.CR.Flat.SupportedInBall R f) {z : ℂ} (hz : R < ‖z‖) :
    Work.CR.Flat.dbarC f z = 0 := by
  have hopen : f =ᶠ[𝓝 z] (fun _ => (0:ℂ)) := by
    apply Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    intro w hw
    exact hfsupp w (le_of_lt hw)
  have hfd : fderiv ℝ f z = 0 := by rw [hopen.fderiv_eq, fderiv_const_apply]
  rw [Work.CR.Flat.dbarC, hfd]
  simp

lemma pompeiu_dbarC_eq_zero_of_le {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall R f) {z : ℂ} (hz : R ≤ ‖z‖) :
    Work.CR.Flat.dbarC f z = 0 := by
  rcases lt_or_eq_of_le hz with h | h
  · exact pompeiu_dbarC_eq_zero_of_lt hfsupp h
  have hcont : Continuous (fun w : ℂ => Work.CR.Flat.dbarC f w) := by
    have h1 : Continuous (fun w : ℂ => fderiv ℝ f w) := hf.continuous_fderiv one_ne_zero
    have h2 : Continuous (fun w : ℂ => fderiv ℝ f w (1:ℂ)) := h1.clm_apply continuous_const
    have h3 : Continuous (fun w : ℂ => fderiv ℝ f w Complex.I) := h1.clm_apply continuous_const
    simp only [Work.CR.Flat.dbarC]
    exact continuous_const.mul (h2.add (continuous_const.mul h3))
  have hmem : z ∈ closure {w : ℂ | R < ‖w‖} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hR2 : (0:ℝ) < 2 * R := by linarith
    refine ⟨(1 + ε / (2 * R)) • z, ?_, ?_⟩
    · change R < ‖(1 + ε / (2 * R)) • z‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← h]
      nlinarith [mul_pos (div_pos hε hR2) hR]
    · rw [Complex.dist_eq]
      have hsub : z - (1 + ε / (2 * R)) • z = (1 - (1 + ε / (2 * R))) • z := by
        nth_rewrite 1 [← one_smul ℝ z]
        rw [← sub_smul]
      rw [hsub, norm_smul, Real.norm_eq_abs, ← h]
      rw [show |1 - (1 + ε / (2 * R))| = ε / (2 * R) by
        rw [show (1 - (1 + ε / (2 * R))) = -(ε / (2 * R)) by ring, abs_neg,
          abs_of_pos (div_pos hε hR2)]]
      rw [show ε / (2 * R) * R = ε / 2 by field_simp]
      linarith
  have him : (fun w : ℂ => Work.CR.Flat.dbarC f w) '' {w : ℂ | R < ‖w‖} ⊆ ({0} : Set ℂ) := by
    rintro y ⟨w, hw, rfl⟩
    exact pompeiu_dbarC_eq_zero_of_lt hfsupp hw
  have h1 : (fun w : ℂ => Work.CR.Flat.dbarC f w) z
      ∈ closure ((fun w : ℂ => Work.CR.Flat.dbarC f w) '' {w : ℂ | R < ‖w‖}) :=
    (image_closure_subset_closure_image hcont) ⟨z, hmem, rfl⟩
  exact closure_minimal him isClosed_singleton h1

/-! ## Integrability of the polar integrand -/

lemma pompeiu_norm_ofReal (r : ℝ) : ‖(r:ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

lemma pompeiu_unit_norm (θ : ℝ) :
    ‖((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)‖ = 1 := by
  have h := Complex.norm_polarCoord_symm (1, θ)
  rw [Complex.polarCoord_symm_apply] at h
  simpa using h

lemma pompeiu_integrableOn_of_bound_target {R C : ℝ} {F : ℝ×ℝ → ℂ}
    (hmeas : Measurable F)
    (hbdd : ∀ p ∈ Complex.polarCoord.target, p.1 ≤ R → ‖F p‖ ≤ C)
    (hz : ∀ p ∈ Complex.polarCoord.target, R < p.1 → F p = 0) :
    IntegrableOn F Complex.polarCoord.target := by
  have hmsS : MeasurableSet {p : ℝ×ℝ | p.1 ≤ R} :=
    (isClosed_le continuous_fst continuous_const).measurableSet
  have hms : MeasurableSet (Complex.polarCoord.target ∩ {p : ℝ×ℝ | p.1 ≤ R}) :=
    Complex.polarCoord.open_target.measurableSet.inter hmsS
  have hset : Complex.polarCoord.target ∩ {p : ℝ×ℝ | p.1 ≤ R}
      = Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [Complex.polarCoord_target, mem_inter_iff, mem_setOf_eq, mem_prod, mem_Ioi, mem_Ioo,
      mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h2, h3⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  have hfin : volume (Complex.polarCoord.target ∩ {p : ℝ×ℝ | p.1 ≤ R}) < ⊤ := by
    rw [hset, Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, Real.volume_Ioc,
      Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hpart1 : IntegrableOn F (Complex.polarCoord.target ∩ {p : ℝ×ℝ | p.1 ≤ R}) := by
    refine IntegrableOn.of_bound hfin
      (hmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self) C ?_
    rw [MeasureTheory.ae_restrict_iff' hms]
    exact Filter.Eventually.of_forall (fun p hp => hbdd p hp.1 hp.2)
  rw [show Complex.polarCoord.target
      = (Complex.polarCoord.target ∩ {p : ℝ×ℝ | p.1 ≤ R})
          ∪ (Complex.polarCoord.target \ {p : ℝ×ℝ | p.1 ≤ R}) by
    ext p; by_cases h : p.1 ≤ R <;> simp [h]]
  rw [integrableOn_union]
  refine ⟨hpart1, ?_⟩
  refine (integrableOn_zero (s := Complex.polarCoord.target \ {p : ℝ×ℝ | p.1 ≤ R})).congr_fun ?_ ?_
  · intro p hp
    exact (hz p hp.1 (not_le.mp hp.2)).symm
  · exact Complex.polarCoord.open_target.measurableSet.diff hmsS

lemma pompeiu_integrableOn_polar_dbar {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall R f) :
    IntegrableOn
        (fun p : ℝ × ℝ => p.1 • (Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)
          / Complex.polarCoord.symm p)) Complex.polarCoord.target
    ∧ IntegrableOn
        (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f (Complex.polarCoord.symm q)) p (1,0))
        Complex.polarCoord.target
    ∧ IntegrableOn
        (fun p : ℝ × ℝ => (Complex.I / (p.1 : ℂ))
          * fderiv ℝ (fun q : ℝ × ℝ => f (Complex.polarCoord.symm q)) p (0,1))
        Complex.polarCoord.target := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  have hG : Continuous (fun p : ℝ×ℝ => fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p) :=
    (hf.comp pompeiu_contDiff_polar_symm).continuous_fderiv one_ne_zero
  have hAcont : Continuous
      (fun p : ℝ×ℝ => fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0)) :=
    hG.clm_apply continuous_const
  have hBcont : Continuous
      (fun p : ℝ×ℝ => fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1)) :=
    hG.clm_apply continuous_const
  have hPhimeas : Measurable
      (fun p : ℝ×ℝ => Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)
        / Complex.polarCoord.symm p) := by
    have h1 : Measurable (fun p : ℝ×ℝ => Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)) := by
      have h2 : Continuous (fun w : ℂ => Work.CR.Flat.dbarC f w) := by
        have h3 : Continuous (fun w : ℂ => fderiv ℝ f w) := hf.continuous_fderiv one_ne_zero
        have h4 : Continuous (fun w : ℂ => fderiv ℝ f w (1:ℂ)) := h3.clm_apply continuous_const
        have h5 : Continuous (fun w : ℂ => fderiv ℝ f w Complex.I) := h3.clm_apply continuous_const
        simp only [Work.CR.Flat.dbarC]
        exact continuous_const.mul (h4.add (continuous_const.mul h5))
      exact h2.measurable.comp (pompeiu_contDiff_polar_symm.continuous.measurable)
    exact h1.div (pompeiu_contDiff_polar_symm.continuous.measurable)
  -- the common bound
  have hccmem : ∀ p ∈ Complex.polarCoord.target, p.1 ≤ R →
      Complex.polarCoord.symm p ∈ Metric.closedBall (0:ℂ) R := by
    intro p hp hpR
    rw [Complex.polarCoord_target] at hp
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
      abs_of_pos hp.1]
    exact hpR
  -- (A) bound
  have hbA : ∀ p ∈ Complex.polarCoord.target, p.1 ≤ R →
      ‖fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0)‖ ≤ C := by
    intro p hp hpR
    rw [Complex.polarCoord_target] at hp
    rw [(pompeiu_fderiv_polarG_apply hf p).1]
    calc ‖fderiv ℝ f (Complex.polarCoord.symm p)
            ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ)*Complex.I)‖
        ≤ ‖fderiv ℝ f (Complex.polarCoord.symm p)‖
            * ‖((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ)*Complex.I)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := by rw [pompeiu_unit_norm, mul_one]
      _ ≤ C := hC _ (hccmem p (by rw [Complex.polarCoord_target]; exact hp) hpR)
  -- (B) bound
  have hbB : ∀ p ∈ Complex.polarCoord.target, p.1 ≤ R →
      ‖(Complex.I / (p.1 : ℂ))
        * fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1)‖ ≤ C := by
    intro p hp hpR
    rw [Complex.polarCoord_target] at hp
    have hp1 : (0:ℝ) < p.1 := hp.1
    rw [(pompeiu_fderiv_polarG_apply hf p).2, norm_mul]
    have hIp : ‖Complex.I / (p.1 : ℂ)‖ = 1 / p.1 := by
      rw [norm_div, Complex.norm_I, pompeiu_norm_ofReal, abs_of_pos hp.1]
    rw [hIp]
    have hcc : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    have hle : ‖fderiv ℝ f (Complex.polarCoord.symm p) (Complex.I * Complex.polarCoord.symm p)‖
        ≤ p.1 * ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := by
      calc ‖fderiv ℝ f (Complex.polarCoord.symm p) (Complex.I * Complex.polarCoord.symm p)‖
          ≤ ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ * ‖Complex.I * Complex.polarCoord.symm p‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ * p.1 := by
            rw [norm_mul, Complex.norm_I, one_mul, hcc]
        _ = p.1 * ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := by ring
    calc 1 / p.1 * ‖fderiv ℝ f (Complex.polarCoord.symm p)
            (Complex.I * Complex.polarCoord.symm p)‖
        ≤ 1 / p.1 * (p.1 * ‖fderiv ℝ f (Complex.polarCoord.symm p)‖) := by
          apply mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := by
          rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hp.1)]
      _ ≤ C := hC _ (hccmem p (by rw [Complex.polarCoord_target]; exact hp) hpR)
  -- (Phi) bound
  have hbPhi : ∀ p ∈ Complex.polarCoord.target, p.1 ≤ R →
      ‖p.1 • (Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)
        / Complex.polarCoord.symm p)‖ ≤ C := by
    intro p hp hpR
    rw [Complex.polarCoord_target] at hp
    have hcc : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    have hb : ‖Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)‖
        ≤ ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := by
      have h3 : Continuous (fun w : ℂ => fderiv ℝ f w) := hf.continuous_fderiv one_ne_zero
      rw [Work.CR.Flat.dbarC, norm_mul]
      have h4 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      rw [h4]
      calc (1/2) * ‖fderiv ℝ f (Complex.polarCoord.symm p) 1
              + Complex.I * fderiv ℝ f (Complex.polarCoord.symm p) Complex.I‖
          ≤ (1/2) * (‖fderiv ℝ f (Complex.polarCoord.symm p) 1‖
              + ‖Complex.I * fderiv ℝ f (Complex.polarCoord.symm p) Complex.I‖) := by
            apply mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ (1/2) * (‖fderiv ℝ f (Complex.polarCoord.symm p)‖ * 1
              + 1 * ‖fderiv ℝ f (Complex.polarCoord.symm p)‖) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply add_le_add
            · simpa using ContinuousLinearMap.le_opNorm
                (fderiv ℝ f (Complex.polarCoord.symm p)) (1:ℂ)
            · simpa [Complex.norm_I] using
                ContinuousLinearMap.le_opNorm (fderiv ℝ f (Complex.polarCoord.symm p)) Complex.I
        _ = ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := by ring
    calc ‖p.1 • (Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)
            / Complex.polarCoord.symm p)‖
        = ‖Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1, norm_div, hcc,
            ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hp.1)]
      _ ≤ ‖fderiv ℝ f (Complex.polarCoord.symm p)‖ := hb
      _ ≤ C := hC _ (hccmem p (by rw [Complex.polarCoord_target]; exact hp) hpR)
  -- vanishing outside `p.1 ≤ R`
  have hGzero : ∀ p : ℝ×ℝ, R < p.1 →
      (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) =ᶠ[𝓝 p] (fun _ => (0:ℂ)) := by
    intro p hpR
    apply Filter.mem_of_superset
      (((isOpen_Ioi (a := R)).prod isOpen_univ).mem_nhds
        (show p ∈ Ioi R ×ˢ (univ : Set ℝ) from ⟨hpR, mem_univ p.2⟩))
    intro q hq
    change f (Complex.polarCoord.symm q) = 0
    apply hfsupp
    rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_trans hR hq.1)]
    exact le_of_lt hq.1
  have hzA : ∀ p ∈ Complex.polarCoord.target, R < p.1 →
      fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0) = 0 := by
    intro p hp hpR
    have hfd : fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p = 0 := by
      rw [(hGzero p hpR).fderiv_eq, fderiv_const_apply]
    rw [hfd]; simp
  have hzB : ∀ p ∈ Complex.polarCoord.target, R < p.1 →
      (Complex.I / (p.1 : ℂ))
        * fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1) = 0 := by
    intro p hp hpR
    have hfd : fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p = 0 := by
      rw [(hGzero p hpR).fderiv_eq, fderiv_const_apply]
    rw [hfd]; simp
  have hzPhi : ∀ p ∈ Complex.polarCoord.target, R < p.1 →
      p.1 • (Work.CR.Flat.dbarC f (Complex.polarCoord.symm p)
        / Complex.polarCoord.symm p) = 0 := by
    intro p hp hpR
    rw [Complex.polarCoord_target] at hp
    have hcc : R < ‖Complex.polarCoord.symm p‖ := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]; exact hpR
    rw [pompeiu_dbarC_eq_zero_of_lt hfsupp hcc]
    simp
  have hmR : Measurable (fun p : ℝ×ℝ => (p.1 : ℂ)) :=
    Complex.ofRealCLM.continuous.measurable.comp measurable_fst
  exact ⟨pompeiu_integrableOn_of_bound_target
            (measurable_fst.smul hPhimeas) hbPhi hzPhi,
         pompeiu_integrableOn_of_bound_target hAcont.measurable hbA hzA,
         pompeiu_integrableOn_of_bound_target
            ((measurable_const.div hmR).mul hBcont.measurable) hbB hzB⟩

/-! ## Pompeiu's formula at the origin -/

lemma pompeiu_cauchyGreen_origin {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall R f) :
    -((Real.pi : ℂ))⁻¹ * ∫ ζ in Metric.ball (0:ℂ) R, (Work.CR.Flat.dbarC f ζ)/ζ = f 0 := by
  obtain ⟨hPhiint, hAint, hBint⟩ := pompeiu_integrableOn_polar_dbar hR hf hfsupp
  have hsupp : ∀ ζ ∉ Metric.ball (0:ℂ) R, (Work.CR.Flat.dbarC f ζ)/ζ = 0 := by
    intro ζ hζ
    rw [Metric.mem_ball] at hζ
    have hζ' : R ≤ ‖ζ‖ := by
      have h := not_lt.mp hζ
      simpa [dist_eq_norm] using h
    rw [pompeiu_dbarC_eq_zero_of_le hR hf hfsupp hζ']
    simp
  have hstep : ∫ ζ in Metric.ball (0:ℂ) R, (Work.CR.Flat.dbarC f ζ)/ζ
      = ∫ p in Complex.polarCoord.target,
          p.1 • ((Work.CR.Flat.dbarC f (Complex.polarCoord.symm p))/Complex.polarCoord.symm p) := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    exact (Complex.integral_comp_polarCoord_symm _).symm
  rw [hstep]
  have hpt : ∀ p ∈ Complex.polarCoord.target,
      p.1 • ((Work.CR.Flat.dbarC f (Complex.polarCoord.symm p))/Complex.polarCoord.symm p)
      = (1/2) * (fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0)
          + (Complex.I/(p.1:ℂ))
            * fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1)) := by
    intro p hp
    rw [Complex.polarCoord_target] at hp
    have hid := pompeiu_polar_dbar_identity hf p hp.1
    change (p.1:ℂ) * ((Work.CR.Flat.dbarC f (Complex.polarCoord.symm p))/Complex.polarCoord.symm p)
      = (1/2) * (fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0)
          + (Complex.I/(p.1:ℂ))
            * fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1))
    rw [hid]
    ring
  rw [MeasureTheory.setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet hpt]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_add hAint hBint]
  have hAval : ∫ p in Complex.polarCoord.target,
      fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0)
      = -((Real.pi:ℂ) * 2) * f 0 := by
    rw [Complex.polarCoord_target]
    conv_lhs => rw [Measure.volume_eq_prod ℝ ℝ]
    rw [← MeasureTheory.setIntegral_prod_swap (Ioi (0:ℝ)) (Ioo (-Real.pi) Real.pi)
          (fun p : ℝ×ℝ => fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (1,0))]
    rw [MeasureTheory.setIntegral_prod (fun q : ℝ×ℝ =>
          fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) q.swap (1,0))
          (MeasureTheory.IntegrableOn.swap hAint)]
    simp only [Prod.swap]
    trans ∫ θ in Ioo (-Real.pi) Real.pi, (- f 0)
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      exact pompeiu_polar_radial_integral hR hf hfsupp θ
    · rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      rw [Complex.real_smul]
      push_cast
      ring
  rw [hAval]
  have hBval : ∫ p in Complex.polarCoord.target,
      (Complex.I/(p.1:ℂ))
        * fderiv ℝ (fun q : ℝ×ℝ => f (Complex.polarCoord.symm q)) p (0,1) = 0 := by
    rw [Complex.polarCoord_target]
    conv_lhs => rw [Measure.volume_eq_prod ℝ ℝ]
    rw [MeasureTheory.setIntegral_prod _ hBint]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with ρ hρ
    rw [MeasureTheory.integral_const_mul]
    rw [pompeiu_polar_angular_integral hf ρ]
    simp
  rw [hBval, add_zero]
  rw [show (1/2 : ℂ) * (-((Real.pi:ℂ) * 2) * f 0) = -((Real.pi:ℂ) * f 0) by ring]
  rw [show -((Real.pi : ℂ))⁻¹ * (-((Real.pi:ℂ) * f 0)) = f 0 by field_simp]

/-! ## The main statement -/

theorem pompeiuFormula {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall R f) {z : ℂ} (hz : ‖z‖ < R) :
    -((Real.pi : ℂ))⁻¹ * ∫ ζ in Metric.ball (0 : ℂ) R, (Work.CR.Flat.dbarC f ζ) / (ζ - z)
      = f z := by
  set g : ℂ → ℂ := fun w => f (z + w) with hg
  have hR' : (0:ℝ) < R + ‖z‖ := by positivity
  have hgdiff : ContDiff ℝ 1 g := by
    rw [hg]
    exact hf.comp
      (by simpa using (contDiff_const.add contDiff_id : ContDiff ℝ 1 (fun x : ℂ => z + x)))
  have hgsupp : Work.CR.Flat.SupportedInBall (R + ‖z‖) g := by
    intro w hw
    rw [hg]
    apply hfsupp
    have h1 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
      have := norm_sub_le (z + w) z
      simpa using this
    linarith
  have hdg : ∀ w, Work.CR.Flat.dbarC g w = Work.CR.Flat.dbarC f (z + w) := by
    intro w
    rw [hg, Work.CR.Flat.dbarC, Work.CR.Flat.dbarC, fderiv_comp_add_left z]
  have hmain : ∫ ζ in Metric.ball (0 : ℂ) R, (Work.CR.Flat.dbarC f ζ) / (ζ - z)
      = ∫ w in Metric.ball (0 : ℂ) (R + ‖z‖), (Work.CR.Flat.dbarC g w) / w := by
    have hA : ∀ ζ ∉ Metric.ball (0:ℂ) R, (Work.CR.Flat.dbarC f ζ)/(ζ - z) = 0 := by
      intro ζ hζ
      rw [Metric.mem_ball] at hζ
      have hζ' : R ≤ ‖ζ‖ := by
        have h := not_lt.mp hζ
        simpa [dist_eq_norm] using h
      rw [pompeiu_dbarC_eq_zero_of_le hR hf hfsupp hζ']
      simp
    have hB : ∀ w ∉ Metric.ball (0:ℂ) (R + ‖z‖), (Work.CR.Flat.dbarC g w)/w = 0 := by
      intro w hw
      rw [Metric.mem_ball] at hw
      have hw' : R + ‖z‖ ≤ ‖w‖ := by
        have h := not_lt.mp hw
        simpa [dist_eq_norm] using h
      rw [pompeiu_dbarC_eq_zero_of_le hR' hgdiff hgsupp hw']
      simp
    calc ∫ ζ in Metric.ball (0:ℂ) R, (Work.CR.Flat.dbarC f ζ)/(ζ - z)
        = ∫ ζ, (Work.CR.Flat.dbarC f ζ)/(ζ - z) :=
          MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hA
      _ = ∫ w, (Work.CR.Flat.dbarC f (z + w))/((z + w) - z) :=
          (MeasureTheory.integral_add_left_eq_self
            (fun ζ => (Work.CR.Flat.dbarC f ζ)/(ζ - z)) z).symm
      _ = ∫ w, (Work.CR.Flat.dbarC g w)/w := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with w
          rw [hdg w]
          congr 1
          ring
      _ = ∫ w in Metric.ball (0:ℂ) (R + ‖z‖), (Work.CR.Flat.dbarC g w)/w :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hB).symm
  rw [hmain]
  rw [pompeiu_cauchyGreen_origin hR' hgdiff hgsupp]
  rw [hg]
  simp

end Work.CR.Flat.Cauchy
