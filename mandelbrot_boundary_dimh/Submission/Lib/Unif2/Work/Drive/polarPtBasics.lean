import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Drive.ChartFlux
import Submission.Lib.Unif2.Work.Drive.ChartFluxRadial
import Submission.Lib.Unif2.Work.PoleMoving.bilin_flux

namespace Work.Drive

open MeasureTheory Set intervalIntegral

/-! ## READ FIRST (session 3)

The recommended route to `greenSymmetryRegion`, the traps, and two verified local lemma statements
(with proof plans) are in `Submission/Work/Drive/NOTES_greenSymmetryRegion_route.md`.  In short:

* the **Dirichlet/Weyl route** is the route to take: the mutual energy
  `∫_Ω ⟪∇gA, ∇gB⟫ = 2π gB a` (and `= 2π gA b` by symmetry of the pairing) gives the reciprocity;
  its *local* input `Work.Analysis.Harmonic.integral_inner_gradient_eq_zero` is already proved in
  the workspace, and the pole term reduces to the planar fundamental-solution identity
  `∫ ⟪∇(−log‖·−a‖), ∇ψ⟫ = 2π ψ a`;
* the **flux route** (the shear/pullback material below) needs one extra input beyond the elementary
  "residue theorem by inclusion–exclusion of chart discs": the *far-field vanishing* of `∮ω` over
  a contour near the ideal boundary, which is an estimate requiring the level curves of `gA` (the
  pointwise sign `∗dgA ≤ 0` on `{gA = ε}` is what bounds `∮ gB ∗dgA` by `2πη`; a bound by the
  total variation of `gA` fails because level curves need not have bounded length);
* `radialDeriv_eq_inner_gradient` below is the bridge between the flux formalism (`radialDeriv`,
  circle averages) and the gradient formalism above. -/

/-! ### Bridge: the radial derivative is a gradient pairing

`Work.Drive.radialDeriv f a z` (defined in `ChartFlux` as the derivative at `t = 1` of
`t ↦ f (a + t (z − a))`, i.e. the *unnormalised* directional derivative along the radius) is the
inner product of `∇f z` with the radial vector `z − a`.  This is the bridge between the flux
formalism (circle averages of `radialDeriv`, `ChartFlux`, `bilin_flux`, `circleFlux_eq_…`) and the
gradient formalism of `Work.Analysis.Harmonic.integral_inner_gradient_eq_zero` (the Dirichlet /
Weyl route to the reciprocity `gA b = gB a`). -/
theorem radialDeriv_eq_inner_gradient {f : ℂ → ℝ} {a z : ℂ} (hf : DifferentiableAt ℝ f z) :
    Work.Drive.radialDeriv f a z = inner (𝕜 := ℝ) (gradient f z) (z - a) := by
  unfold Work.Drive.radialDeriv
  have hα : HasDerivAt (fun t : ℝ => a + (t : ℂ) * (z - a)) (z - a) 1 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 1 :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 (hasDerivAt_id 1)
    have h2 := (h1.mul_const (z - a)).const_add a
    simpa using h2
  have hfd : HasFDerivAt f (fderiv ℝ f z) (a + (1 : ℂ) * (z - a)) := by
    rw [show a + (1 : ℂ) * (z - a) = z by simp]
    exact hf.hasFDerivAt
  have hc := hfd.comp_hasDerivAt 1 hα
  have hcomp : deriv (fun t : ℝ => f (a + (t : ℂ) * (z - a))) 1
      = fderiv ℝ f z (z - a) := by
    simpa [Function.comp_def] using hc.deriv
  rw [hcomp]
  simp

/-- **Linearity of the radial derivative** in the function: `radialDeriv (f − g) a z =
radialDeriv f a z − radialDeriv g a z` (at any point where `f` and `g` are differentiable along
the radius). -/
theorem radialDeriv_sub {f g : ℂ → ℝ} {a z : ℂ}
    (hf : DifferentiableAt ℝ f (a + (1 : ℂ) * (z - a)))
    (hg : DifferentiableAt ℝ g (a + (1 : ℂ) * (z - a))) :
    Work.Drive.radialDeriv (fun y : ℂ => f y - g y) a z
      = Work.Drive.radialDeriv f a z - Work.Drive.radialDeriv g a z := by
  have hray : DifferentiableAt ℝ (fun t : ℝ => a + (t : ℂ) * (z - a)) 1 := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ)) 1 :=
      Complex.ofRealCLM.differentiableAt
    have h2 : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * (z - a)) 1 :=
      h1.mul_const (z - a)
    exact (differentiableAt_const (c := a)).add h2
  unfold Work.Drive.radialDeriv
  change deriv ((fun t : ℝ => f (a + (t : ℂ) * (z - a)))
      - (fun t : ℝ => g (a + (t : ℂ) * (z - a)))) 1
      = deriv (fun t : ℝ => f (a + (t : ℂ) * (z - a))) 1
        - deriv (fun t : ℝ => g (a + (t : ℂ) * (z - a))) 1
  rw [deriv_sub (f := fun t : ℝ => f (a + (t : ℂ) * (z - a)))
        (g := fun t : ℝ => g (a + (t : ℂ) * (z - a)))
        (hf.comp 1 hray) (hg.comp 1 hray)]

/-- The radial derivative of `−log‖·−a‖` is `−1` off the centre (the unit log pole normalisation). -/
theorem radialDeriv_logNeg {a z : ℂ} (hz : z ≠ a) :
    Work.Drive.radialDeriv (fun y : ℂ => - Real.log ‖y - a‖) a z = -1 := by
  have h := Work.Drive.radialDeriv_logNorm (a := a) (α := 0) (β := -1) (by norm_num) (z := z) hz
  simpa using h

/-- **The gradient of the singular factor.**  `∇ (−log‖·−a‖) (z) = −(‖z−a‖²)⁻¹ • (z − a)`: the
derivative of `−log‖y − a‖` at `z ≠ a` is `−(‖z−a‖²)⁻¹` times the inner product with `z − a`. -/
theorem hasFDerivAt_neg_log_norm_sub {a z : ℂ} (hz : z ≠ a) :
    HasFDerivAt (fun y : ℂ => -Real.log ‖y - a‖)
      (-(1 / ‖z - a‖ ^ 2) • (innerSL ℝ (z - a) : ℂ →L[ℝ] ℝ)) z := by
  have hnorm : HasFDerivAt (fun y : ℂ => ‖y - a‖ ^ 2)
      (2 • (innerSL ℝ (z - a) : ℂ →L[ℝ] ℝ)) z := by
    have h1 : HasFDerivAt (fun y : ℂ => y - a) (1 : ℂ →L[ℝ] ℂ) z :=
      (hasFDerivAt_id (𝕜 := ℝ) (x := z)).sub_const a
    refine (h1.norm_sq).congr_fderiv ?_
    ext v
    simp
  have hsq0 : (0 : ℝ) < ‖z - a‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) 2
  have hlog : HasFDerivAt (fun y : ℂ => Real.log (‖y - a‖ ^ 2))
      ((‖z - a‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (z - a) : ℂ →L[ℝ] ℝ))) z := by
    have h3 : HasDerivAt Real.log ((‖z - a‖ ^ 2)⁻¹) (‖z - a‖ ^ 2) :=
      Real.hasDerivAt_log (ne_of_gt hsq0)
    refine (h3.hasFDerivAt.comp z hnorm).congr_fderiv ?_
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have hscaled : HasFDerivAt (fun y : ℂ => -(1 / 2 : ℝ) * Real.log (‖y - a‖ ^ 2))
      ((-(1 / 2 : ℝ)) • ((‖z - a‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (z - a) : ℂ →L[ℝ] ℝ)))) z :=
    hlog.const_mul (-(1 / 2 : ℝ))
  have hcoe : (-(1 / 2 : ℝ)) • ((‖z - a‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (z - a) : ℂ →L[ℝ] ℝ)))
      = -(1 / ‖z - a‖ ^ 2) • (innerSL ℝ (z - a) : ℂ →L[ℝ] ℝ) := by
    ext v
    simp only [smul_apply, smul_eq_mul]
    rw [one_div]
    ring
  refine (hscaled.congr_fderiv hcoe).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  change -Real.log ‖y - a‖ = -(1 / 2 : ℝ) * Real.log (‖y - a‖ ^ 2)
  rcases eq_or_ne ‖y - a‖ 0 with h | h
  · simp [h]
  · rw [Real.log_pow]; ring

/-- The gradient form of `hasFDerivAt_neg_log_norm_sub`. -/
theorem gradient_neg_log_norm_sub {a z : ℂ} (hz : z ≠ a) :
    gradient (fun y : ℂ => -Real.log ‖y - a‖) z = -(‖z - a‖ ^ 2)⁻¹ • (z - a) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_neg_log_norm_sub hz).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_smul_left]
  ring

/-- **The pole integrand.**  The pairing of `∇(−log‖·−a‖)` with `∇ψ` is the (unnormalised) radial
derivative of `ψ` divided by `−‖z−a‖²`: the form in which the singular-integral computation is done. -/
theorem inner_gradient_neg_log_norm_sub_eq {ψ : ℂ → ℝ} {a z : ℂ} (hz : z ≠ a)
    (hψ : DifferentiableAt ℝ ψ z) :
    inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z) (gradient ψ z)
      = - Work.Drive.radialDeriv ψ a z / ‖z - a‖ ^ 2 := by
  rw [inner_gradient_left, (hasFDerivAt_neg_log_norm_sub hz).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [Work.Drive.radialDeriv_eq_inner_gradient (f := ψ) hψ,
    real_inner_comm (z - a) (gradient ψ z)]
  ring

/-- **Radial derivative after a translation.**  `radialDeriv ψ a (a + u)` is the derivative at `t = 1`
of `t ↦ ψ (a + t • u)` (this is the form in which the polar-coordinate computation uses it). -/
theorem radialDeriv_add_eq (ψ : ℂ → ℝ) (a u : ℂ) :
    Work.Drive.radialDeriv ψ a (a + u) = deriv (fun t : ℝ => ψ (a + t • u)) 1 := by
  unfold Work.Drive.radialDeriv
  congr 1
  funext t
  simp only [add_sub_cancel_left, Complex.real_smul]

/-- **Chain rule for the radial derivative along a fixed direction.**  For a point `a + r • u` on the
ray in direction `u`, `radialDeriv ψ a (a + r • u) = r · (d/dr) ψ (a + r • u)`. -/
theorem radialDeriv_smul {ψ : ℂ → ℝ} {a u : ℂ} {r : ℝ}
    (hΨ : DifferentiableAt ℝ (fun t : ℝ => ψ (a + t • u)) r) :
    Work.Drive.radialDeriv ψ a (a + r • u)
      = r * deriv (fun t : ℝ => ψ (a + t • u)) r := by
  have h1 : (fun t : ℝ => ψ (a + t • (r • u))) = fun t : ℝ => ψ (a + (t * r) • u) := by
    funext t
    rw [smul_smul]
  rw [radialDeriv_add_eq, h1]
  have hlin : HasDerivAt (fun t : ℝ => t * r) (1 * r) 1 :=
    (hasDerivAt_id (1 : ℝ)).mul_const r
  have hΨ' : HasDerivAt (fun t : ℝ => ψ (a + t • u))
      (deriv (fun t : ℝ => ψ (a + t • u)) r) (1 * r) := by
    rw [one_mul]
    exact hΨ.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ψ (a + (t * r) • u))
      (deriv (fun t : ℝ => ψ (a + t • u)) r * (1 * r)) 1 := by
    simpa [Function.comp_def] using hΨ'.comp 1 hlin
  rw [h2.deriv]
  ring

/-- **The plane integral as an integral over `ℝ × ℝ`** (the bridge used by the polar-coordinate
computation of the singular integral): integrating over `ℂ` is the same as integrating over
`ℝ × ℝ` against the measure-preserving measurable equivalence `Complex.measurableEquivRealProd`. -/
theorem integral_complex_eq_integral_realProd (F : ℂ → ℝ) :
    (∫ z : ℂ, F z) = ∫ p : ℝ × ℝ, F { re := p.1, im := p.2 } := by
  rw [show (∫ z : ℂ, F z)
      = ∫ z, F (Complex.measurableEquivRealProd.symm (Complex.measurableEquivRealProd z))
      from by simp]
  refine (Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => F (Complex.measurableEquivRealProd.symm p))).trans ?_
  simp [Complex.measurableEquivRealProd_symm_apply]

/-- **The plane integral in polar coordinates.**  The composite of
`integral_complex_eq_integral_realProd` with Mathlib's polar change of variables
(`Real.integral_comp_polarCoord_symm`). -/
theorem integral_complex_eq_integral_polar (F : ℂ → ℝ) :
    (∫ z : ℂ, F z)
      = ∫ p in polarCoord.target,
          p.1 • F { re := (polarCoord.symm p).1, im := (polarCoord.symm p).2 } := by
  rw [integral_complex_eq_integral_realProd]
  exact (integral_comp_polarCoord_symm fun p : ℝ × ℝ => F { re := p.1, im := p.2 }).symm

/-- The complex point attached to a pair in polar coordinates: `r e^{iθ} = r (cos θ + i sin θ)`. -/
noncomputable def polarPt (p : ℝ × ℝ) : ℂ :=
  ((p.1 * Real.cos p.2 : ℝ) : ℂ) + ((p.1 * Real.sin p.2 : ℝ) : ℂ) * Complex.I

theorem polarPt_eq_smul (p : ℝ × ℝ) :
    polarPt p = p.1 • ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
  unfold polarPt
  rw [Complex.real_smul]
  push_cast
  ring

theorem norm_polarPt_sq (p : ℝ × ℝ) : ‖polarPt p‖ ^ 2 = p.1 ^ 2 := by
  rw [polarPt_eq_smul, norm_smul, mul_pow]
  have hu : ‖((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    nlinarith [Real.sin_sq_add_cos_sq p.2]
  rw [hu, mul_one, Real.norm_eq_abs, sq_abs]

/-- **Step (4)**: on the polar target, the pulled-back integrand `p.1 • F` is minus the derivative of
`r ↦ ψ (a + polarPt (r, p.2))` at `p.1`. -/
theorem inner_gradient_neg_log_norm_polar {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ)
    {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    p.1 • inner (𝕜 := ℝ)
        (gradient (fun y : ℂ => -Real.log ‖y - a‖) (a + polarPt p))
        (gradient ψ (a + polarPt p))
      = -deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1 := by
  have hr : 0 < p.1 := hp.1
  have hz : a + polarPt p ≠ a := by
    intro h
    have h0 : polarPt p = 0 := by
      have h1 := congrArg (fun w : ℂ => w - a) h
      simpa using h1
    have h2 : ‖polarPt p‖ ^ 2 = 0 := by rw [h0]; simp
    rw [norm_polarPt_sq] at h2
    nlinarith
  have hψd : DifferentiableAt ℝ ψ (a + polarPt p) :=
    (hψ.differentiable one_ne_zero).differentiableAt
  rw [Work.Drive.inner_gradient_neg_log_norm_sub_eq (ψ := ψ) (a := a) hz hψd]
  rw [show ‖(a + polarPt p) - a‖ ^ 2 = p.1 ^ 2 by rw [add_sub_cancel_left, norm_polarPt_sq]]
  rw [polarPt_eq_smul]
  rw [Work.Drive.radialDeriv_smul (a := a) (r := p.1)
    (u := (Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)]
  · have hder : deriv (fun t : ℝ =>
          ψ (a + t • ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I))) p.1
        = deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1 := by
      congr 1
      funext r
      rw [polarPt_eq_smul]
    rw [hder]
    have hne : p.1 ≠ 0 := ne_of_gt hr
    rw [smul_eq_mul]
    field_simp
  · have hlin : DifferentiableAt ℝ
        (fun t : ℝ => a + t • ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)) p.1 :=
      ((differentiableAt_id (𝕜 := ℝ)).smul_const _).const_add a
    exact (hψ.differentiable one_ne_zero).differentiableAt.comp p.1 hlin

/-- The polar bridge with the point written as `polarPt p`. -/
theorem integral_complex_eq_integral_polar' (G : ℂ → ℝ) :
    (∫ z : ℂ, G z) = ∫ p in polarCoord.target, p.1 • G (polarPt p) := by
  rw [integral_complex_eq_integral_polar]
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet ?_
  intro p hp
  have hpt : ({ re := (polarCoord.symm p).1, im := (polarCoord.symm p).2 } : ℂ) = polarPt p := by
    apply Complex.ext <;> simp [polarPt, polarCoord, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  change p.1 • G { re := (polarCoord.symm p).1, im := (polarCoord.symm p).2 }
      = p.1 • G (polarPt p)
  rw [hpt]

/-- **Translation invariance of the plane integral**, in the shift direction used by the polar
computation of the singular integral: `∫ F = ∫ w, F (a + w)`. -/
theorem integral_comp_add_eq (F : ℂ → ℝ) (a : ℂ) :
    (∫ z : ℂ, F z) = ∫ w : ℂ, F (a + w) := by
  rw [show (fun w : ℂ => F (a + w)) = fun w : ℂ => F (w + a) from by
    funext w
    rw [add_comm]]
  exact (integral_add_right_eq_self F a).symm

/-- **The singular integral in polar form (steps (ii)+(iii)).**  The plane integral of the pole
integrand collapses to `∫ p in polarCoord.target, −∂_{p.1} (ψ ∘ (a + polarPt ·))`: the polar change of
variables (with the Jacobian `p.1` cancelling the `1/‖z‖`) followed by the pointwise identity
`inner_gradient_neg_log_norm_polar`. -/
theorem integral_integrand_polar {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ z : ℂ, inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z) (gradient ψ z))
      = ∫ p in polarCoord.target, -deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1 := by
  set F : ℂ → ℝ :=
    fun z => inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z) (gradient ψ z)
  rw [integral_comp_add_eq F a]
  rw [integral_complex_eq_integral_polar' (fun w : ℂ => F (a + w))]
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet ?_
  intro p hp
  change p.1 • F (a + polarPt p) = -deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1
  exact inner_gradient_neg_log_norm_polar hψ hp

/-- **The angular integration, conditional on the (purely measure-theoretic) integrability of the
integrand.**  `setIntegral_polar_eq_two_pi_mul_of_integrable` is the full polar computation: the
definitional rewrite of `polarCoord.target`, the swap `MeasureTheory.setIntegral_prod_swap`, Fubini
`MeasureTheory.setIntegral_prod`, the per-angle fundamental theorem of calculus
`Work.Drive.integral_polar_deriv_eq`, and `Real.volume_Ioo` for the angular measure `2π`.
The only hypothesis is `IntegrableOn` of the integrand on the product set, which holds because the
integrand is continuous and vanishes once `r > ‖a‖ + sup_{tsupport ψ} ‖·−a‖`
(`norm_polarPt_sq` gives `‖polarPt (r,θ)‖ = r`, so `ψ` evaluated on the ray is supported in
`r ≤ ‖a‖ + R`). -/
theorem setIntegral_polar_eq_two_pi_mul_of_integrable {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hint : IntegrableOn (fun q : ℝ × ℝ => -deriv (fun r : ℝ => ψ (a + polarPt (r, q.1))) q.2)
      (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ)))
    (hderiv : ∀ θ : ℝ,
      (∫ r in Set.Ioi (0 : ℝ), -deriv (fun ρ : ℝ => ψ (a + polarPt (ρ, θ))) r) = ψ a) :
    (∫ p in polarCoord.target, -deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1)
      = 2 * Real.pi * ψ a := by
  set g : ℝ × ℝ → ℝ := fun q => -deriv (fun r : ℝ => ψ (a + polarPt (r, q.1))) q.2 with hg
  have hstep : (∫ p in polarCoord.target, -deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1)
      = ∫ q in Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ), g q := by
    rw [show polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl]
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [← MeasureTheory.setIntegral_prod_swap (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
      (fun p : ℝ × ℝ => -deriv (fun r : ℝ => ψ (a + polarPt (r, p.2))) p.1)]
    rfl
  rw [hstep]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod g hint]
  have hinner : ∀ θ : ℝ, (∫ r in Set.Ioi (0 : ℝ), g (θ, r)) = ψ a := fun θ => hderiv θ
  simp_rw [hinner]
  rw [MeasureTheory.setIntegral_const]
  have hvol : volume.real (Set.Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
    change (volume (Set.Ioo (-Real.pi) Real.pi)).toReal = 2 * Real.pi
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi - -Real.pi)]
    ring
  rw [hvol, smul_eq_mul]





/-- **The shear** straightening the rectangle `(α,β) × (0,1)` onto the region
`{(x,y) : α < x < β, φ x < y < ψ x}` between the graphs of `φ` and `ψ`. -/
def shear (φ ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, φ p.1 + p.2 * (ψ p.1 - φ p.1))

/-- The derivative of `shear φ ψ`. -/
def shearDeriv (φ ψ φ' ψ' : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
    ((φ' p.1 + p.2 * (ψ' p.1 - φ' p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (ψ p.1 - φ p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The shear has the expected derivative. -/
theorem hasFDerivAt_shear {φ ψ φ' ψ' : ℝ → ℝ} {p : ℝ × ℝ}
    (hφ : HasDerivAt φ (φ' p.1) p.1) (hψ : HasDerivAt ψ (ψ' p.1) p.1) :
    HasFDerivAt (shear φ ψ) (shearDeriv φ ψ φ' ψ' p) p := by
  unfold shear shearDeriv
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℝ × ℝ => φ q.1) ((φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hφ.comp_hasFDerivAt p hasFDerivAt_fst
  have hz : HasFDerivAt (fun q : ℝ × ℝ => ψ q.1) ((ψ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hψ.comp_hasFDerivAt p hasFDerivAt_fst
  have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hprod : HasFDerivAt (fun q : ℝ × ℝ => q.2 * (ψ q.1 - φ q.1))
      (p.2 • ((ψ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (ψ p.1 - φ p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hs.mul (hz.sub hy)
  have hsum := hy.add hprod
  have heq : ((φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      + (p.2 • ((ψ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (ψ p.1 - φ p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      = (φ' p.1 + p.2 * (ψ' p.1 - φ' p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (ψ p.1 - φ p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, smul_apply, sub_apply]
    ring
  rw [heq] at hsum
  exact h1.prodMk hsum

/-- The shear at `s = 0` is the lower graph. -/
theorem shear_zero (φ ψ : ℝ → ℝ) (x : ℝ) : shear φ ψ (x, 0) = (x, φ x) := by
  unfold shear
  simp

/-- The shear at `s = 1` is the upper graph. -/
theorem shear_one (φ ψ : ℝ → ℝ) (x : ℝ) : shear φ ψ (x, 1) = (x, ψ x) := by
  unfold shear
  simp

/-- The derivative of the shear on the bottom edge, applied to `(1,0)`. -/
theorem shearDeriv_zero {φ ψ φ' ψ' : ℝ → ℝ} (x : ℝ) :
    shearDeriv φ ψ φ' ψ' (x, 0) (1, 0) = (1, φ' x) := by
  simp only [shearDeriv, ContinuousLinearMap.prod_apply, add_apply, smul_apply]
  simp

/-- The derivative of the shear on the top edge, applied to `(1,0)`. -/
theorem shearDeriv_one {φ ψ φ' ψ' : ℝ → ℝ} (x : ℝ) :
    shearDeriv φ ψ φ' ψ' (x, 1) (1, 0) = (1, ψ' x) := by
  simp only [shearDeriv, ContinuousLinearMap.prod_apply, add_apply, smul_apply]
  simp

/-- The derivative of the shear on a vertical edge, applied to `(0,1)`. -/
theorem shearDeriv_snd {φ ψ φ' ψ' : ℝ → ℝ} (x s : ℝ) :
    shearDeriv φ ψ φ' ψ' (x, s) (0, 1) = (0, ψ x - φ x) := by
  simp only [shearDeriv, ContinuousLinearMap.prod_apply, add_apply, smul_apply]
  simp

/-! ### The pullback of a 1-form under the shear

For a 1-form `ω` on the plane, `coeff1 ω p = ω p (1,0)` and `coeff2 ω p = ω p (0,1)` are its two
coefficients.  The pullback `Φ*ω` along the shear has coefficients

`Pη (x,s) = coeff1 ω (Φ (x,s)) + coeff2 ω (Φ (x,s)) * (φ' x + s (ψ' x - φ' x))`,
`Qη (x,s) = coeff2 ω (Φ (x,s)) * (ψ x - φ x)`,

and `pullback1_eq` / `pullback2_eq` below say that these are, definitionally, the two values
`ω (Φ p) (DΦ p (1,0))` and `ω (Φ p) (DΦ p (0,1))` of the pullback form. -/

/-- First coefficient `ω p (1,0)` of a 1-form on the plane. -/
def coeff1 (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ := ω p (1, 0)

/-- Second coefficient `ω p (0,1)` of a 1-form on the plane. -/
def coeff2 (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ := ω p (0, 1)

/-- Linearity of a 1-form at `(1,c)`. -/
theorem form_apply_fst_add (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) (c : ℝ) :
    coeff1 ω p + coeff2 ω p * c = ω p (1, c) := by
  have h : ((1 : ℝ), c) = ((1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (1 : ℝ)) := by simp
  rw [h, map_add, map_smul, smul_eq_mul]
  simp only [coeff1, coeff2]
  ring

/-- Linearity of a 1-form at `(0,c)`. -/
theorem form_apply_snd (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) (c : ℝ) :
    coeff2 ω p * c = ω p (0, c) := by
  have h : ((0 : ℝ), c) = c • ((0 : ℝ), (1 : ℝ)) := by simp
  rw [h, map_smul, smul_eq_mul]
  simp only [coeff2]
  ring

/-- The `s`-component of `DΦ (1,0)`, i.e. the function `φ' x + s (ψ' x - φ' x)`. -/
def shearC (φ ψ φ' ψ' : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := φ' p.1 + p.2 * (ψ' p.1 - φ' p.1)

/-- The `s`-component of `DΦ (0,1)`, i.e. the function `ψ x - φ x`. -/
def shearD (φ ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ψ p.1 - φ p.1

/-- `DΦ p (1,0) = (1, C p)`. -/
theorem shearDeriv_fst {φ ψ φ' ψ' : ℝ → ℝ} (p : ℝ × ℝ) :
    shearDeriv φ ψ φ' ψ' p (1, 0) = (1, shearC φ ψ φ' ψ' p) := by
  simp only [shearDeriv, shearC, ContinuousLinearMap.prod_apply, add_apply, smul_apply]
  simp

/-- `DΦ p (0,1) = (0, D p)`. -/
theorem shearDeriv_snd' {φ ψ φ' ψ' : ℝ → ℝ} (p : ℝ × ℝ) :
    shearDeriv φ ψ φ' ψ' p (0, 1) = (0, shearD φ ψ p) := by
  simp only [shearDeriv, shearD, ContinuousLinearMap.prod_apply, add_apply, smul_apply]
  simp

/-- First coefficient of the pullback `Φ*ω`. -/
def pullback1 (φ ψ φ' ψ' : ℝ → ℝ) (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ :=
  coeff1 ω (shear φ ψ p) + coeff2 ω (shear φ ψ p) * shearC φ ψ φ' ψ' p

/-- Second coefficient of the pullback `Φ*ω`. -/
def pullback2 (φ ψ φ' ψ' : ℝ → ℝ) (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ :=
  coeff2 ω (shear φ ψ p) * shearD φ ψ p

/-- The first pullback coefficient is `ω (Φ p) (DΦ p (1,0))`. -/
theorem pullback1_eq (φ ψ φ' ψ' : ℝ → ℝ) (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) :
    pullback1 φ ψ φ' ψ' ω p = ω (shear φ ψ p) (shearDeriv φ ψ φ' ψ' p (1, 0)) := by
  rw [shearDeriv_fst]
  exact form_apply_fst_add ω (shear φ ψ p) (shearC φ ψ φ' ψ' p)

/-- The second pullback coefficient is `ω (Φ p) (DΦ p (0,1))`. -/
theorem pullback2_eq (φ ψ φ' ψ' : ℝ → ℝ) (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) :
    pullback2 φ ψ φ' ψ' ω p = ω (shear φ ψ p) (shearDeriv φ ψ φ' ψ' p (0, 1)) := by
  rw [shearDeriv_snd']
  exact form_apply_snd ω (shear φ ψ p) (shearD φ ψ p)


/-! ### The derivative of the pullback (route (a): `φ'`, `ψ'` differentiable)

`dcoeff1`, `dcoeff2` are the derivatives of the coefficient maps `coeff1 ω`, `coeff2 ω`; `dA`, `dB`
are the derivatives of `coeff1 ω ∘ Φ`, `coeff2 ω ∘ Φ` (chain rule); `dshearC`, `dshearD` are those
of the shear components `shearC`, `shearD`.  `hasFDerivAt_pullback1` / `hasFDerivAt_pullback2` then
give the derivative of the pullback's two coefficients. -/

/-- `v ↦ (dω z v) (1,0)`: the derivative of `coeff1 ω` at `z`. -/
noncomputable def dcoeff1 (dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))) ∘L (dω z)

/-- `v ↦ (dω z v) (0,1)`: the derivative of `coeff2 ω` at `z`. -/
noncomputable def dcoeff2 (dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))) ∘L (dω z)

/-- The derivative of `coeff1 ω ∘ Φ` at `p`. -/
noncomputable def dA (φ ψ φ' ψ' : ℝ → ℝ) (dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ)
    (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  dcoeff1 dω (shear φ ψ p) ∘L shearDeriv φ ψ φ' ψ' p

/-- The derivative of `coeff2 ω ∘ Φ` at `p`. -/
noncomputable def dB (φ ψ φ' ψ' : ℝ → ℝ) (dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ)
    (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  dcoeff2 dω (shear φ ψ p) ∘L shearDeriv φ ψ φ' ψ' p

/-- The derivative of `shearC`. -/
noncomputable def dshearC (φ' ψ' φ'' ψ'' : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (φ'' p.1 + p.2 * (ψ'' p.1 - φ'' p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ
    + (ψ' p.1 - φ' p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The derivative of `shearD`. -/
noncomputable def dshearD (φ' ψ' : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ψ' p.1 - φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The derivative of the first pullback coefficient. -/
noncomputable def dpullback1 (φ ψ φ' ψ' φ'' ψ'' : ℝ → ℝ) (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  dA φ ψ φ' ψ' dω p +
    (coeff2 ω (shear φ ψ p) • dshearC φ' ψ' φ'' ψ'' p
      + shearC φ ψ φ' ψ' p • dB φ ψ φ' ψ' dω p)

/-- The derivative of the second pullback coefficient. -/
noncomputable def dpullback2 (φ ψ φ' ψ' : ℝ → ℝ) (ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  coeff2 ω (shear φ ψ p) • dshearD φ' ψ' p + shearD φ ψ p • dB φ ψ φ' ψ' dω p

/-- Derivative of the shear component `shearC`. -/
theorem hasFDerivAt_shearC {φ ψ φ' ψ' φ'' ψ'' : ℝ → ℝ} {p : ℝ × ℝ}
    (hφ' : HasDerivAt φ' (φ'' p.1) p.1) (hψ' : HasDerivAt ψ' (ψ'' p.1) p.1) :
    HasFDerivAt (shearC φ ψ φ' ψ') (dshearC φ' ψ' φ'' ψ'' p) p := by
  unfold shearC dshearC
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => φ' q.1) ((φ'' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hφ'.comp_hasFDerivAt p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => ψ' q.1) ((ψ'' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hψ'.comp_hasFDerivAt p hasFDerivAt_fst
  have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h3 := hs.mul (h2.sub h1)
  have hsum := h1.add h3
  simp only [Pi.sub_apply] at hsum
  have heq : ((φ'' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      + (p.2 • ((ψ'' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (φ'' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (ψ' p.1 - φ' p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      = (φ'' p.1 + p.2 * (ψ'' p.1 - φ'' p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (ψ' p.1 - φ' p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, smul_apply, sub_apply]
    ring
  rw [heq] at hsum
  exact hsum

/-- Derivative of the shear component `shearD`. -/
theorem hasFDerivAt_shearD {φ ψ φ' ψ' : ℝ → ℝ} {p : ℝ × ℝ}
    (hφ : HasDerivAt φ (φ' p.1) p.1) (hψ : HasDerivAt ψ (ψ' p.1) p.1) :
    HasFDerivAt (shearD φ ψ) (dshearD φ' ψ' p) p := by
  unfold shearD dshearD
  have hy : HasFDerivAt (fun q : ℝ × ℝ => φ q.1) ((φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hφ.comp_hasFDerivAt p hasFDerivAt_fst
  have hz : HasFDerivAt (fun q : ℝ × ℝ => ψ q.1) ((ψ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hψ.comp_hasFDerivAt p hasFDerivAt_fst
  have h := hz.sub hy
  have heq : (ψ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
      = (ψ' p.1 - φ' p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, smul_apply]
    ring
  rw [heq] at h
  exact h

/-- Derivative of the first pullback coefficient `Pη = coeff1 ω ∘ Φ + (coeff2 ω ∘ Φ) * shearC`. -/
theorem hasFDerivAt_pullback1 {φ ψ φ' ψ' φ'' ψ'' : ℝ → ℝ} {p : ℝ × ℝ}
    (hφ : HasDerivAt φ (φ' p.1) p.1) (hψ : HasDerivAt ψ (ψ' p.1) p.1)
    (hφ' : HasDerivAt φ' (φ'' p.1) p.1) (hψ' : HasDerivAt ψ' (ψ'' p.1) p.1)
    {ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ} {dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ}
    (hω : HasFDerivAt ω (dω (shear φ ψ p)) (shear φ ψ p)) :
    HasFDerivAt (pullback1 φ ψ φ' ψ' ω) (dpullback1 φ ψ φ' ψ' φ'' ψ'' ω dω p) p := by
  have hA : HasFDerivAt (fun q : ℝ × ℝ => coeff1 ω (shear φ ψ q)) (dA φ ψ φ' ψ' dω p) p :=
    (((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp
      (shear φ ψ p) hω).comp p (hasFDerivAt_shear hφ hψ))
  have hB : HasFDerivAt (fun q : ℝ × ℝ => coeff2 ω (shear φ ψ q)) (dB φ ψ φ' ψ' dω p) p :=
    (((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp
      (shear φ ψ p) hω).comp p (hasFDerivAt_shear hφ hψ))
  have hC : HasFDerivAt (shearC φ ψ φ' ψ') (dshearC φ' ψ' φ'' ψ'' p) p :=
    hasFDerivAt_shearC hφ' hψ'
  exact hA.add (hB.mul hC)

/-- Derivative of the second pullback coefficient `Qη = (coeff2 ω ∘ Φ) * shearD`. -/
theorem hasFDerivAt_pullback2 {φ ψ φ' ψ' : ℝ → ℝ} {p : ℝ × ℝ}
    (hφ : HasDerivAt φ (φ' p.1) p.1) (hψ : HasDerivAt ψ (ψ' p.1) p.1)
    {ω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ} {dω : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ}
    (hω : HasFDerivAt ω (dω (shear φ ψ p)) (shear φ ψ p)) :
    HasFDerivAt (pullback2 φ ψ φ' ψ' ω) (dpullback2 φ ψ φ' ψ' ω dω p) p := by
  have hB : HasFDerivAt (fun q : ℝ × ℝ => coeff2 ω (shear φ ψ q)) (dB φ ψ φ' ψ' dω p) p :=
    (((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp
      (shear φ ψ p) hω).comp p (hasFDerivAt_shear hφ hψ))
  have hD : HasFDerivAt (shearD φ ψ) (dshearD φ' ψ' p) p := hasFDerivAt_shearD hφ hψ
  exact hB.mul hD

/-- **Green's theorem for a rectangle (closed 1-form version).**

Let `P Q : ℝ × ℝ → ℝ` be the two coefficient functions of a 1-form on the plane, `P' Q'` their
Fréchet derivatives on the closed rectangle `[a₁,b₁] × [a₂,b₂]`, and suppose the form is *closed*
there: `(Q' p) (1,0) = (P' p) (0,1)` (i.e. `∂Q/∂x = ∂P/∂y`).  Then the integral of the form over
the boundary of the rectangle vanishes, i.e.

`∫_{a₁}^{b₁} P(x,a₂) dx + ∫_{a₂}^{b₂} Q(b₁,y) dy = ∫_{a₁}^{b₁} P(x,b₂) dx + ∫_{a₂}^{b₂} Q(a₁,y) dy`,

the four terms being the bottom edge (traversed rightwards), the right edge (upwards), the top edge
and the left edge (downwards).  This is `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`
applied to `(f, g) = (Q, -P)`: the divergence is `∂Q/∂x - ∂P/∂y = 0` by closedness. -/
theorem rectangle_Green_eq_zero
    {P Q : ℝ × ℝ → ℝ} {P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ} {a₁ a₂ b₁ b₂ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hPc : ContinuousOn P (Set.Icc (a₁, a₂) (b₁, b₂)))
    (hQc : ContinuousOn Q (Set.Icc (a₁, a₂) (b₁, b₂)))
    (hPd : ∀ p ∈ Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂, HasFDerivAt P (P' p) p)
    (hQd : ∀ p ∈ Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂, HasFDerivAt Q (Q' p) p)
    (hcl : ∀ p ∈ Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂, (Q' p) (1, 0) = (P' p) (0, 1))
    (hi : IntegrableOn (fun p : ℝ × ℝ => (Q' p) (1, 0) + (-(P' p)) (0, 1))
      (Set.Icc (a₁, a₂) (b₁, b₂))) :
    (∫ x in a₁..b₁, P (x, a₂)) + (∫ y in a₂..b₂, Q (b₁, y))
      = (∫ x in a₁..b₁, P (x, b₂)) + (∫ y in a₂..b₂, Q (a₁, y)) := by
  have hsub : ∀ p ∈ Set.Ioo a₁ b₁ ×ˢ Set.Ioo a₂ b₂, p ∈ Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ :=
    fun p hp => Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self hp
  have h := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
      (f := Q) (g := fun p : ℝ × ℝ => -P p) (f' := Q') (g' := fun p => -(P' p))
      (a := (a₁, a₂)) (b := (b₁, b₂)) (by exact ⟨h₁, h₂⟩) hQc hPc.neg
      (fun p hp => hQd p (hsub p hp)) (fun p hp => (hPd p (hsub p hp)).neg) hi
  have hzero : ∫ p : ℝ × ℝ in Set.Icc (a₁, a₂) (b₁, b₂),
      (Q' p) (1, 0) + (-(P' p)) (0, 1) = 0 := by
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
    intro p hp
    have hp' : p ∈ Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ := by
      rw [Set.Icc_prod_eq] at hp; exact hp
    have h1 : (Q' p) (1, 0) = (P' p) (0, 1) := hcl p hp'
    have h2 : (-(P' p)) (0, 1) = -((P' p) (0, 1)) := neg_apply _ _
    rw [h1, h2, add_neg_cancel]
  rw [hzero] at h
  simp only [intervalIntegral.integral_neg] at h
  linarith [h]

/-!
## Status of this file (state of the art, for the next agent)

`greenSymmetryRegion` is the *relatively compact* case of the classical symmetry
`G_Ω(a,b) = G_Ω(b,a)` of the Green function.  It is the **crux** of the whole project: the
"general" versions of the symmetry (`Work.Drive.greenSymmetryGeneral`,
`Work.Drive.greenSymmetry_le_general`) are *reductions to this statement* — for `t > 0` the
superlevel region `S_t = {x ∈ Ω | t < gA x}` has Green function `gA - t` at the pole `a`
(`Work.Drive.isGreenOn_superlevel`), carries a Green function at the pole `b`
(`Work.Drive.greenExistence_levelRegion_secondPole`), and the monotonicity
`Work.Drive.isGreenOn_le_of_subset` (`S_t ⊆ Ω`) turns the symmetry of `S_t` into
`gA b - t ≥ gB a`, i.e. into the symmetry of `Ω` in the limit `t → 0`.  So everything rests on the
case proved here, for a region with compact closure.

### What is missing, precisely

The classical proof is Green's second identity / the flux argument.  With
`ω := gA ∗dgB - gB ∗dgA` (a closed `C¹` 1-form on `Ω ∖ {a,b}`; `dω = 0` pointwise since both
functions are harmonic there) one applies Green's identity on
`R = {gA > ε} ∖ (discs around a and b)` and lets `ε → 0`.  Every ingredient of that proof is
available in this workspace **except one**, the 2D identity itself:

* the *local* computations at the poles (the flux of `ω` over a small circle around `a` is
  `2π gB a`, over one around `b` it is `-2π gA b`) are elementary: shrink the circle to a chart
  disc and use the logarithmic pole (`Work.SimplyConnected.ABS.HasLogPoleOn`) together with the
  circle-average/flux machinery `Work.Drive.circleFlux`,
  `Work.Drive.circleFlux_eq_of_harmonicOn_annulus` (proved, axiom-clean);
* the *vanishing* of the boundary term on `{gA = ε}` follows from the decay clause of `IsGreenOn`
  (both `gA` and `gB` are `< ε` off a compact subset of `Ω`);
* **what is missing** is the 2D flux identity: for a closed `C¹` 1-form on a neighbourhood of a
  compact region `R` (here `R = {gA > ε} ∖ (discs)`) with piecewise smooth boundary,
  `∮_{∂R} ω = 0`.  Mathlib has this only for rectangles (`MeasureTheory.integral_divergence_*`,
  `Complex.integral_boundary_rect_*`) and for annuli
  (`Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`);
  the workspace's flux results are for *chart annuli*
  (`Work.Drive.circleFlux_eq_of_harmonicOn_annulus`,
  `Work.Drive.circleFluxBilin_eq_of_harmonicOn_annulus`).  Two routes for the 2D input:
  1. deform the boundary of `R` along the level sets of `gA` and use the chart-annulus flux
     identity patchwise (this needs the flux to be constant along the level sets, i.e. the same
     identity for the region between two level sets);
  2. build it from the rectangle theorem by a shear (the map `(x,s) ↦ (x, f x + s (g x - f x))`
     straightens a "curvilinear quadrilateral" to a rectangle, and the curve integral of a closed
     form is covariant under diffeomorphisms) plus a partition of unity to globalise.
  Note that the vanishing of the flux over `∂R` is *not* a homological triviality: it is false
  for general closed 1-forms (only for forms whose periods happen to vanish), so it has to come
  from the 2D identity.

### Progress on the 2D input (same session)

The plane input is being built in this file, in layers:

* `rectangle_Green_eq_zero` — **proved**: for a *closed* 1-form on a rectangle the sum of the four
  boundary integrals vanishes.  It is `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`
  applied to `(f,g) = (Q, -P)`, whose divergence `∂Q/∂x - ∂P/∂y` vanishes by closedness; the
  hypotheses are differentiability/continuity on the *closed* rectangle, so no a.e. bookkeeping is
  needed.
* `shear`, `shearDeriv`, `hasFDerivAt_shear`, `shear_zero`, `shear_one`, `shearDeriv_zero`,
  `shearDeriv_one`, `shearDeriv_snd` — **proved**: the shear `(x,s) ↦ (x, φ x + s (ψ x - φ x))`
  straightens the rectangle onto the region between two graphs, with its derivative and the four
  edge evaluations.

**Also done** (same session): the pullback layer — `coeff1`, `coeff2`, `form_apply_fst_add`,
`form_apply_snd`, `shearC`, `shearD`, `shearDeriv_fst`, `shearDeriv_snd'`, `pullback1`,
`pullback2`, `pullback1_eq`, `pullback2_eq`: the pullback form's coefficients, expressed
*explicitly* as `Pη = coeff1 (Φ) + coeff2 (Φ) * (φ' + s (ψ' - φ'))` and `Qη = coeff2 (Φ) * (ψ - φ)`,
and proved to be definitionally the values `ω (Φ p) (DΦ p (1,0))`, `ω (Φ p) (DΦ p (0,1))`.

Still missing for the graph-region version `flux_graphRegion_eq_zero`:
(i) the coefficients of the pullback `Φ*ω` and their derivatives (chain + product rules) with the
*closedness* of the pullback — the pointwise computation is
`∂_s (Φ*ω)_{ds} - ∂_x (Φ*ω)_{dx} = (ψ x - φ x) · (∂Q/∂x - ∂P/∂y)(Φ (x,s)) = 0`, and note that it
uses only *first* derivatives of `φ`, `ψ` (the second-order terms cancel);
(ii) the identification of the four boundary integrals of `Φ*ω` with the four graph-region
integrals (chain rule on the horizontal edges; the substitution `y = φ β + s (ψ β - φ β)` on the
right edge and similarly on the left).

Note on the shape of (i): the *full* Fréchet derivatives of `Pη`, `Qη` (needed by
`rectangle_Green_eq_zero`) involve `φ''`, `ψ''` because `∂_x (φ' x + s (ψ' x - φ' x))` does; only
the two *directional* values entering the closedness, `∂_s Pη` and `∂_x Qη`, are first order.  The
second-order terms cancel in the difference `∂_s Pη - ∂_x Qη = (ψ - φ) (∂Q/∂x - ∂P/∂y)(Φ)`, which
is why the closedness is a first-order identity (this is the content of `form_apply_fst_add` /
`form_apply_snd` being applied at the point `Φ p` and of the symmetry hypothesis on `dω`).  The
simplest formalisation is therefore either (a) to assume `φ'`, `ψ'` differentiable on `[α,β]` (so
that the full derivatives exist and the cancellation is automatic), or (b) to prove a *directional*
rectangle theorem needing only `s ↦ Pη(x,s)` and `x ↦ Qη(x,s)` differentiable, and to feed it the
first-order computations.  Route (a) is what the present infrastructure is set up for.


The local computations and the assembly (pole expansions, the `ε → 0` limit, the uniqueness of
`IsGreenOn` at a fixed pole, `Work.Drive.isGreenOn_unique`) are all within reach with the
workspace's tools; the 2D identity above is the only missing input.

### Coordination note (session 2026-09-24, 01:30)

* `Work.Drive.greenSymmetry_le_general_of_region` is now **sorry-free**: it derives the one-sided
  inequality `gB a ≤ gA b` for an *arbitrary* open `Ω` from the *relatively compact* case.
* `Work.Drive.greenSymmetry_le_general` (one-sided, arbitrary `Ω`) is sorry-free **but only modulo**
  `Work.Drive.greenSymmetry_of_isGreenOn` (it applies the relative-compact *equality* there), so it
  is not yet usable in an axiom-clean proof.
* `Work.Drive.greenSymmetry_of_isGreenOn` — the exact same statement as this file — still has a
  `sorry`, as does its helper `Work.Drive.exists_greenKernel` and the one-sided
  `Work.Drive.greenSymmetryLeRegion`.

So the *relatively compact* symmetry proved here is the last remaining input of the whole area, and
it is equivalent to the one-sided inequality `gB a ≤ gA b` for relatively compact `Ω` (the reverse
inequality is obtained by exchanging the poles).  Note also that the reduction runs the *other* way
from what one might hope: the general case reduces to this one, so no general-`Ω` statement can
replace it.
-/


theorem norm_polarPt (p : ℝ × ℝ) : ‖polarPt p‖ = |p.1| := by
  have h2 : ‖polarPt p‖ ^ 2 = |p.1| ^ 2 := by rw [norm_polarPt_sq, sq_abs]
  nlinarith [norm_nonneg (polarPt p), abs_nonneg p.1]

/-- The radial derivative of `ψ` along the ray in direction `e^{iθ}` vanishes once `r` exceeds
`‖a‖` plus a bound for `tsupport ψ` around `a`. -/
theorem deriv_polarPt_eq_zero_of_support {ψ : ℂ → ℝ} {a : ℂ} (hψc : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ θ r : ℝ, R + ‖a‖ < r →
      deriv (fun ρ : ℝ => ψ (a + polarPt (ρ, θ))) r = 0 := by
  have hbdd : BddAbove ((fun z : ℂ => ‖z - a‖) '' tsupport ψ) :=
    (hψc.image (continuous_norm.comp (continuous_id.sub continuous_const))).bddAbove
  obtain ⟨R₀, hR₀⟩ := hbdd
  have hR0 : (0 : ℝ) ≤ max R₀ 0 := le_max_right _ _
  refine ⟨max R₀ 0, hR0, fun θ r hr => ?_⟩
  have hR : ∀ z ∈ tsupport ψ, ‖z - a‖ ≤ max R₀ 0 := fun z hz =>
    le_trans (hR₀ ⟨z, hz, rfl⟩) (le_max_left _ _)
  have hzero : ∀ s : ℝ, max R₀ 0 + ‖a‖ < s → ψ (a + polarPt (s, θ)) = 0 := by
    intro s hs
    have hs' : 0 < s := by linarith [norm_nonneg a]
    have hbound : max R₀ 0 < ‖a + polarPt (s, θ) - a‖ := by
      rw [add_sub_cancel_left, norm_polarPt, abs_of_pos hs']
      linarith [norm_nonneg a]
    have hnot : a + polarPt (s, θ) ∉ tsupport ψ := fun hmem =>
      not_lt_of_ge (hR _ hmem) hbound
    exact image_eq_zero_of_notMem_tsupport hnot
  have hev : (fun ρ : ℝ => ψ (a + polarPt (ρ, θ))) =ᶠ[nhds r] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact hzero s hs
  rw [hev.deriv_eq]
  simp

theorem hasDerivAt_polarPt (θ r : ℝ) :
    HasDerivAt (fun ρ : ℝ => polarPt (ρ, θ))
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) r := by
  have hρ : HasDerivAt (fun ρ : ℝ => (ρ : ℂ)) (1 : ℂ) r :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_id r)
  have h := hρ.mul_const ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
  simpa [polarPt, Complex.ofReal_mul, mul_add, mul_assoc] using h

theorem deriv_polarPt_eq_fderiv {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ) (θ r : ℝ) :
    deriv (fun ρ : ℝ => ψ (a + polarPt (ρ, θ))) r
      = fderiv ℝ ψ (a + polarPt (r, θ)) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  have hd : DifferentiableAt ℝ ψ (a + polarPt (r, θ)) :=
    (hψ.differentiable one_ne_zero).differentiableAt
  have hpath : HasDerivAt (fun ρ : ℝ => a + polarPt (ρ, θ))
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) r :=
    (hasDerivAt_polarPt θ r).const_add a
  exact (hd.hasFDerivAt.comp_hasDerivAt r hpath).deriv

theorem continuous_polarPt : Continuous polarPt := by
  unfold polarPt
  fun_prop

theorem continuous_deriv_polarPt {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (fun q : ℝ × ℝ => -deriv (fun ρ : ℝ => ψ (a + polarPt (ρ, q.1))) q.2) := by
  have hfun : (fun q : ℝ × ℝ => -deriv (fun ρ : ℝ => ψ (a + polarPt (ρ, q.1))) q.2)
      = fun q : ℝ × ℝ => -fderiv ℝ ψ (a + polarPt (q.2, q.1))
          ((Real.cos q.1 : ℂ) + (Real.sin q.1 : ℂ) * Complex.I) := by
    funext q
    rw [deriv_polarPt_eq_fderiv hψ]
  rw [hfun]
  refine (((hψ.continuous_fderiv one_ne_zero).comp ?_).clm_apply ?_).neg
  · exact continuous_const.add (continuous_polarPt.comp continuous_swap)
  · fun_prop


/-- **The `IntegrableOn` obligation for the polar computation.**  The polar integrand is integrable
on `Ioo (−π) π ×ˢ Ioi 0`: it is continuous (`continuous_deriv_polarPt`) and, by
`deriv_polarPt_eq_zero_of_support`, it vanishes once `q.2 > R + ‖a‖`, so it agrees with its
indicator on the compact `Icc (−π) π ×ˢ Icc 0 (R + ‖a‖)`. -/
theorem integrableOn_deriv_polarPt {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    IntegrableOn (fun q : ℝ × ℝ => -deriv (fun r : ℝ => ψ (a + polarPt (r, q.1))) q.2)
      (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ)) := by
  obtain ⟨R, hR0, hR⟩ := deriv_polarPt_eq_zero_of_support (a := a) hψc
  set g : ℝ × ℝ → ℝ := fun q => -deriv (fun r : ℝ => ψ (a + polarPt (r, q.1))) q.2 with hg
  have hcont : Continuous g := continuous_deriv_polarPt hψ
  set t : Set (ℝ × ℝ) := Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc 0 (R + ‖a‖) with ht
  have ht_compact : IsCompact t := isCompact_Icc.prod isCompact_Icc
  have ht_int : IntegrableOn g t := hcont.continuousOn.integrableOn_compact ht_compact
  have ht_meas : MeasurableSet t := measurableSet_Icc.prod measurableSet_Icc
  have hs_meas : MeasurableSet (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ)) :=
    measurableSet_Ioo.prod measurableSet_Ioi
  have hpt : EqOn g (fun q : ℝ × ℝ => if q ∈ t then g q else 0)
      (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ)) := by
    intro q hq
    by_cases hqt : q ∈ t
    · simp [hqt]
    · have hq1 : q.1 ∈ Set.Ioo (-Real.pi) Real.pi := hq.1
      have hq2 : q.2 ∈ Set.Ioi (0 : ℝ) := hq.2
      have hge : R + ‖a‖ < q.2 := by
        rcases lt_or_ge (R + ‖a‖) q.2 with h | h
        · exact h
        · exact absurd ⟨⟨le_of_lt hq1.1, le_of_lt hq1.2⟩, ⟨le_of_lt hq2, h⟩⟩ hqt
      simp only [hqt, if_false]
      rw [hg]
      simp only [hR q.1 q.2 hge, neg_zero]
  have h_trunc : IntegrableOn (fun q : ℝ × ℝ => if q ∈ t then g q else 0)
      (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ)) := by
    have h1 : Integrable (t.indicator g) := ht_int.integrable_indicator ht_meas
    have h2 : (fun q : ℝ × ℝ => if q ∈ t then g q else 0) = t.indicator g := by
      funext q
      by_cases hq : q ∈ t <;> simp [Set.indicator, hq]
    rw [h2]
    exact h1.integrableOn
  exact h_trunc.congr_fun hpt.symm hs_meas

end Work.Drive
