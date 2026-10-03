import Mathlib
import Submission.Lib.Unif2.Work.Drive.ChartFlux
import Submission.Lib.Unif2.Work.Drive.circleFlux_eq_of_harmonicOn_annulus
import Submission.Lib.Unif2.Work.Drive.SubharmonicZeroExtension

set_option maxHeartbeats 800000

/-!
# The radial model of the flux identity

`Work.Drive.circleFlux_eq_of_harmonicOn_annulus` is the bridge between the circle means of a harmonic
function on an annulus and its flux.  This module proves the *model case* of that identity, i.e. for
the radial harmonic function `z ↦ α + β * Real.log ‖z - a‖` on the annulus with radii `0 < r ≤ r'`:

* `Work.Drive.radialDeriv_logNorm` — its radial derivative is the constant `β`;
* `Work.Drive.circleAverage_logNorm` — its circle mean at radius `s > 0` is `α + β * Real.log s`;
* `Work.Drive.circleFlux_logNorm` — its flux through every circle of radius `s ≠ 0` is `2 * π * β`;
* `Work.Drive.circleAverage_sub_eq_flux_log_div_logNorm` — the identity of
  `circleFlux_eq_of_harmonicOn_annulus` holds, with the *same* constant `2 * π`.

This pins the normalisation of `Work.Drive.circleFlux` (a wrong constant there would invalidate every
downstream statement) and is the template for the general case, where the same identity is integrated
in `s` from `r` to `r'` along the radii.
-/

namespace Work.Drive

open MeasureTheory intervalIntegral Filter
open scoped Topology

/-- The circle mean of a constant is that constant. -/
theorem circleAverage_const' (c : ℝ) (a : ℂ) (r : ℝ) :
    Real.circleAverage (fun _ : ℂ => c) a r = c := by
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have h : (fun θ : ℝ => (fun _ : ℂ => c) (circleMap a r θ)) = fun _ : ℝ => c := by
    funext θ; rfl
  rw [Real.circleAverage_def, h, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp

section Model

variable {a : ℂ} {α β : ℝ}

/-- **The radial derivative of the model** `z ↦ α + β * log ‖z - a‖` is the constant `β` off the
centre. -/
theorem radialDeriv_logNorm (hβ : β ≠ 0) {z : ℂ} (hz : z ≠ a) :
    radialDeriv (fun w : ℂ => α + β * Real.log ‖w - a‖) a z = β := by
  set c : ℝ := ‖z - a‖ with hc
  have hcpos : 0 < c := by rw [hc]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have h1 : (fun t : ℝ => α + β * Real.log ‖(a + (t : ℂ) * (z - a)) - a‖)
      = fun t : ℝ => α + β * Real.log (|t| * c) := by
    funext t
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : (fun t : ℝ => α + β * Real.log (|t| * c))
      =ᶠ[𝓝 (1 : ℝ)] fun t : ℝ => α + β * Real.log (t * c) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [abs_of_pos ht]
  have hderiv : deriv (fun t : ℝ => α + β * Real.log (t * c)) 1 = β := by
    have hev : (fun t : ℝ => α + β * Real.log (t * c))
        =ᶠ[𝓝 (1 : ℝ)] fun t : ℝ => α + β * (Real.log t + Real.log c) := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
      rw [Real.log_mul (ne_of_gt ht) (ne_of_gt hcpos)]
    rw [hev.deriv_eq]
    have : deriv (fun t : ℝ => α + β * (Real.log t + Real.log c)) 1 = β := by
      have hlog : HasDerivAt Real.log (1⁻¹) 1 := Real.hasDerivAt_log (x := (1 : ℝ)) (by norm_num)
      have hc : HasDerivAt (fun t : ℝ => α + β * (Real.log t + Real.log c)) (β * 1⁻¹) 1 :=
        ((hlog.add_const (Real.log c)).const_mul β).const_add α
      have hval : β * 1⁻¹ = β := by simp
      rw [hc.deriv, hval]
    rw [this]
  rw [radialDeriv, h1, h2.deriv_eq, hderiv]

/-- **The circle mean of the model** at radius `r > 0` is `α + β * log r`. -/
theorem circleAverage_logNorm {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w : ℂ => α + β * Real.log ‖w - a‖) a r
      = α + β * Real.log r := by
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have h : (fun θ : ℝ => α + β * Real.log ‖circleMap a r θ - a‖)
      = fun _ : ℝ => α + β * Real.log r := by
    funext θ
    have hnorm : ‖circleMap a r θ - a‖ = r := by
      rw [circleMap, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, Complex.mul_I_re]
      simp [abs_of_pos hr]
    rw [hnorm]
  rw [Real.circleAverage_def, h, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp

/-- **The flux of the model** through the circle of radius `r ≠ 0` is `2 * π * β`. -/
theorem circleFlux_logNorm (hβ : β ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    circleFlux (fun w : ℂ => α + β * Real.log ‖w - a‖) a r = 2 * Real.pi * β := by
  have hcongr : (fun z : ℂ => radialDeriv (fun w : ℂ => α + β * Real.log ‖w - a‖) a z)
      =ᶠ[codiscreteWithin (Metric.sphere a |r|)] fun _ : ℂ => β := by
    filter_upwards [self_mem_codiscreteWithin (Metric.sphere a |r|)] with z hz
    refine radialDeriv_logNorm hβ ?_
    intro hza
    subst hza
    simp at hz
    exact hr (abs_eq_zero.mp hz.symm)
  rw [circleFlux, Real.circleAverage_congr_codiscreteWithin hcongr hr, circleAverage_const']

/-- **The model case of `Work.Drive.circleFlux_eq_of_harmonicOn_annulus`.** -/
theorem circleAverage_sub_eq_flux_log_div_logNorm (hβ : β ≠ 0) {r r' : ℝ}
    (hr : 0 < r) (hr' : 0 < r') :
    Real.circleAverage (fun w : ℂ => α + β * Real.log ‖w - a‖) a r'
        - Real.circleAverage (fun w : ℂ => α + β * Real.log ‖w - a‖) a r
      = circleFlux (fun w : ℂ => α + β * Real.log ‖w - a‖) a r
          * Real.log (r' / r) / (2 * Real.pi) := by
  rw [circleAverage_logNorm hr', circleAverage_logNorm hr,
    circleFlux_logNorm hβ (ne_of_gt hr), Real.log_div (ne_of_gt hr') (ne_of_gt hr)]
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp
  ring

/-- **The dictionary between `radialDeriv` and the derivative along a circle.**  For `s ≠ 0` and
`V` differentiable at the point `circleMap a s θ` of the circle,

`radialDeriv V a (circleMap a s θ) = s * deriv (fun σ => V (circleMap a σ θ)) s`

(the radial derivative is the derivative in the direction `z - a`, whose length is `s`).  This is the
identity that turns `circleFlux V a r = 2 * π * (mean of the radial derivative)` into
`2 * π * r * d/dr (circle mean)`. -/
theorem radialDeriv_circleMap {V : ℂ → ℝ} {a : ℂ} {θ s : ℝ}
    (hV : DifferentiableAt ℝ V (circleMap a s θ)) (hs : s ≠ 0) :
    radialDeriv V a (circleMap a s θ)
      = s * deriv (fun σ : ℝ => V (circleMap a σ θ)) s := by
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hcm : ∀ σ : ℝ, circleMap a σ θ = a + (σ : ℂ) * e := by
    intro σ; rw [circleMap, he]
  -- the radial derivative, in the parametrisation `σ ↦ a + σ * e`
  have harg : ∀ t : ℝ,
      V (a + (t : ℂ) * (circleMap a s θ - a)) = V (a + ((t * s : ℝ) : ℂ) * e) := by
    intro t
    congr 1
    rw [hcm s, add_sub_cancel_left]
    push_cast
    ring
  have hrad : radialDeriv V a (circleMap a s θ)
      = deriv (fun t : ℝ => V (a + ((t * s : ℝ) : ℂ) * e)) 1 := by
    rw [radialDeriv]
    exact congrArg (fun f : ℝ → ℝ => deriv f 1) (funext harg)
  -- the two curves
  have hsm : ((s : ℂ) * e) = s • e := by rw [Complex.real_smul]
  have hV' : DifferentiableAt ℝ V (a + (s : ℂ) * e) := by
    rw [← hcm s]; exact hV
  have hgam : HasDerivAt (fun σ : ℝ => a + (σ : ℂ) * e) e s := by
    have h := (((hasDerivAt_id s).ofReal_comp).mul_const e).const_add a
    simpa only [id_eq, Complex.ofReal_one, one_mul, mul_one] using h
  have hd2 : deriv (fun σ : ℝ => V (a + (σ : ℂ) * e)) s
      = (fderiv ℝ V (a + (s : ℂ) * e)) e := by
    have h := (hV'.hasFDerivAt).comp_hasDerivAt s hgam
    simpa only [Function.comp_def] using h.deriv
  have hga : HasDerivAt (fun t : ℝ => a + ((t * s : ℝ) : ℂ) * e) ((s : ℂ) * e) 1 := by
    have h := ((((hasDerivAt_id (1 : ℝ)).mul_const s).ofReal_comp).mul_const e).const_add a
    simpa only [id_eq, Complex.ofReal_one, one_mul, mul_one] using h
  have hpt : a + ((1 * s : ℝ) : ℂ) * e = a + (s : ℂ) * e := by rw [one_mul]
  have hV'' : DifferentiableAt ℝ V (a + ((1 * s : ℝ) : ℂ) * e) := by rw [hpt]; exact hV'
  have hd1 : deriv (fun t : ℝ => V (a + ((t * s : ℝ) : ℂ) * e)) 1
      = (fderiv ℝ V (a + (s : ℂ) * e)) e * s := by
    have h1 := (hV''.hasFDerivAt).comp_hasDerivAt 1 hga
    have h3 : deriv (fun t : ℝ => V (a + ((t * s : ℝ) : ℂ) * e)) 1
        = (fderiv ℝ V (a + ((1 * s : ℝ) : ℂ) * e)) ((s : ℂ) * e) := by
      simpa only [Function.comp_def] using h1.deriv
    have h2 : deriv (fun t : ℝ => V (a + ((t * s : ℝ) : ℂ) * e)) 1
        = (fderiv ℝ V (a + (s : ℂ) * e)) ((s : ℂ) * e) := by
      rw [h3, hpt]
    rw [h2, hsm, map_smul, smul_eq_mul]
    ring
  rw [hrad, hd1]
  simp only [hcm]
  rw [hd2]
  ring

/-- The form of `radialDeriv_circleMap` used by the FTC along radii: the derivative of `V` along the
circle map is the radial derivative divided by the radius. -/
theorem deriv_circleMap_eq_radialDeriv_div {V : ℂ → ℝ} {a : ℂ} {θ s : ℝ}
    (hV : DifferentiableAt ℝ V (circleMap a s θ)) (hs : s ≠ 0) :
    deriv (fun σ : ℝ => V (circleMap a σ θ)) s
      = radialDeriv V a (circleMap a s θ) / s := by
  rw [radialDeriv_circleMap hV hs]
  field_simp

/-- **The fundamental theorem of calculus along one radius.**  For `0 < r ≤ r'`, a function `V`
differentiable along the radius `θ` between `r` and `r'`, and with the radial derivative integrable
there,

`V (circleMap a r' θ) - V (circleMap a r θ) = ∫ s in r..r', radialDeriv V a (circleMap a s θ) / s`.

This is the per-`θ` input of `circleAverage V a r' - circleAverage V a r = ∫ s in r..r', …`; the
integrand is `deriv_circleMap_eq_radialDeriv_div`, applied verbatim. -/
theorem circleMap_sub_eq_integral_radialDeriv_div {V : ℂ → ℝ} {a : ℂ} {θ r r' : ℝ}
    (hr : 0 < r) (hrr' : r ≤ r')
    (hH : ∀ s : ℝ, r ≤ s → s ≤ r' → DifferentiableAt ℝ V (circleMap a s θ))
    (hcont : ContinuousOn (fun s : ℝ => radialDeriv V a (circleMap a s θ) / s) (Set.uIcc r r')) :
    V (circleMap a r' θ) - V (circleMap a r θ)
      = ∫ s in r..r', radialDeriv V a (circleMap a s θ) / s := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun σ : ℝ => V (circleMap a σ θ)) (fun s hs => ?_) hcont.intervalIntegrable).symm
  have hsI : s ∈ Set.Icc r r' := by rwa [Set.uIcc_of_le hrr'] at hs
  obtain ⟨hsr, hsr'⟩ := Set.mem_Icc.mp hsI
  have hs0 : s ≠ 0 := ne_of_gt (lt_of_lt_of_le hr hsr)
  have hcurve : DifferentiableAt ℝ (fun σ : ℝ => circleMap a σ θ) s := by
    have h : DifferentiableAt ℝ (fun σ : ℝ => a + (σ : ℂ) * Complex.exp (θ * Complex.I)) s :=
      (Complex.differentiable_ofReal.differentiableAt.mul_const
        (Complex.exp (θ * Complex.I))).const_add a
    simpa only [circleMap] using h
  have hcomp : DifferentiableAt ℝ (fun σ : ℝ => V (circleMap a σ θ)) s :=
    (hH s hsr hsr').comp s hcurve
  have hder : HasDerivAt (fun σ : ℝ => V (circleMap a σ θ))
      (deriv (fun σ : ℝ => V (circleMap a σ θ)) s) s := hcomp.hasDerivAt
  rw [deriv_circleMap_eq_radialDeriv_div (hH s hsr hsr') hs0] at hder
  exact hder

/-- **First move of the averaging step.**  The difference of the two circle means is `(2 * π)⁻¹` times
the integral of the pointwise difference along the two circles (linearity of the interval integral and
of the scalar multiplication), with the integrability of each circle trace as the only side condition.
-/
theorem circleAverage_sub_eq_smul_integral_sub {V : ℂ → ℝ} {a : ℂ} {r r' : ℝ}
    (h₁ : IntervalIntegrable (fun θ : ℝ => V (circleMap a r' θ)) volume 0 (2 * Real.pi))
    (h₂ : IntervalIntegrable (fun θ : ℝ => V (circleMap a r θ)) volume 0 (2 * Real.pi)) :
    Real.circleAverage V a r' - Real.circleAverage V a r
      = (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi,
          (V (circleMap a r' θ) - V (circleMap a r θ)) := by
  rw [Real.circleAverage_def, Real.circleAverage_def]
  rw [intervalIntegral.integral_sub h₁ h₂, mul_sub]
  simp only [smul_eq_mul]

/-- **Second move of the averaging step.**  Substituting the per-`θ` fundamental theorem of calculus
(`circleMap_sub_eq_integral_radialDeriv_div`) into the averaged difference of the circle means. -/
theorem circleAverage_sub_eq_smul_integral_integral {V : ℂ → ℝ} {a : ℂ} {r r' : ℝ}
    (hr : 0 < r) (hrr' : r ≤ r')
    (hH : ∀ s : ℝ, r ≤ s → s ≤ r' → ∀ θ : ℝ, DifferentiableAt ℝ V (circleMap a s θ))
    (hcont : ∀ θ : ℝ,
      ContinuousOn (fun s : ℝ => radialDeriv V a (circleMap a s θ) / s) (Set.uIcc r r'))
    (h₁ : IntervalIntegrable (fun θ : ℝ => V (circleMap a r' θ)) volume 0 (2 * Real.pi))
    (h₂ : IntervalIntegrable (fun θ : ℝ => V (circleMap a r θ)) volume 0 (2 * Real.pi)) :
    Real.circleAverage V a r' - Real.circleAverage V a r
      = (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi,
          ∫ s in r..r', radialDeriv V a (circleMap a s θ) / s := by
  rw [circleAverage_sub_eq_smul_integral_sub h₁ h₂]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact circleMap_sub_eq_integral_radialDeriv_div hr hrr'
    (fun s hs hs' => hH s hs hs' θ) (hcont θ)

/-- **The swap brick.**  Fubini for the iterated interval integrals on the compact rectangle
`[0, 2π] × [r, r']`, in the form used by the averaging step:  the only side condition is the
integrability of the uncurried integrand for the product of the restricted volumes (supplied in the
application by `ContinuousOn.integrableOn_compact` of the integrand on the compact rectangle). -/
theorem smul_integral_integral_swap {G : ℝ → ℝ → ℝ} {r r' : ℝ}
    (hr : 0 < r) (hrr : r ≤ r')
    (hint : Integrable (Function.uncurry G)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (volume.restrict (Set.Ioc r r')))) :
    (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, ∫ s in r..r', G θ s
      = (2 * Real.pi)⁻¹ * ∫ s in r..r', ∫ θ in 0..2 * Real.pi, G θ s := by
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  congr 1
  simp only [intervalIntegral.integral_of_le h2, intervalIntegral.integral_of_le hrr]
  exact MeasureTheory.integral_integral_swap hint

/-- **The circle-mean/flux identity for a differentiable function.**  For `0 < r ≤ r'`,

`circleAverage V a r' - circleAverage V a r = ∫ s in r..r', circleAverage (radialDeriv V a ·) a s / s`,

i.e. the circle mean grows at rate `flux / (2 * π s)`.  This is the identity that
`Work.Drive.circleFlux_eq_of_harmonicOn_annulus` is built from: for a *harmonic* `V` the integrand is
constant in `s` (`2 * π * circleAverage (radialDeriv V a ·) a s = circleFlux V a s`). -/
theorem circleAverage_sub_eq_integral_circleAverage {V : ℂ → ℝ} {a : ℂ} {r r' : ℝ}
    (hr : 0 < r) (hrr' : r ≤ r')
    (hH : ∀ s : ℝ, r ≤ s → s ≤ r' → ∀ θ : ℝ, DifferentiableAt ℝ V (circleMap a s θ))
    (hcont : ∀ θ : ℝ,
      ContinuousOn (fun s : ℝ => radialDeriv V a (circleMap a s θ) / s) (Set.uIcc r r'))
    (h₁ : IntervalIntegrable (fun θ : ℝ => V (circleMap a r' θ)) volume 0 (2 * Real.pi))
    (h₂ : IntervalIntegrable (fun θ : ℝ => V (circleMap a r θ)) volume 0 (2 * Real.pi))
    (hint : Integrable (Function.uncurry (fun θ s : ℝ => radialDeriv V a (circleMap a s θ) / s))
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (volume.restrict (Set.Ioc r r')))) :
    Real.circleAverage V a r' - Real.circleAverage V a r
      = ∫ s in r..r', Real.circleAverage (fun z : ℂ => radialDeriv V a z) a s / s := by
  rw [circleAverage_sub_eq_smul_integral_integral hr hrr' hH hcont h₁ h₂,
    smul_integral_integral_swap hr hrr' hint]
  have hG : ∀ s : ℝ, (∫ θ in 0..2 * Real.pi, radialDeriv V a (circleMap a s θ) / s)
      = 2 * Real.pi * Real.circleAverage (fun z : ℂ => radialDeriv V a z) a s / s := by
    intro s
    rw [intervalIntegral.integral_div, Real.circleAverage_def]
    simp only [smul_eq_mul]
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp
  have hfac : ∀ s : ℝ, 2 * Real.pi * Real.circleAverage (fun z : ℂ => radialDeriv V a z) a s / s
      = 2 * Real.pi * (Real.circleAverage (fun z : ℂ => radialDeriv V a z) a s / s) := by
    intro s; ring
  simp only [hG, hfac]
  rw [intervalIntegral.integral_const_mul]
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp

/-- **Shift invariance of the circle mean.**  Recentring the function and the centre does not change
the mean — the step that transfers `harmonic_annulus_fourier_structure` (proved for annuli centred at
`0`) to an annulus centred at `a`. -/
theorem circleAverage_comp_add (V : ℂ → ℝ) (a : ℂ) (r : ℝ) :
    Real.circleAverage (fun z : ℂ => V (z + a)) 0 r = Real.circleAverage V a r :=
  Real.circleAverage_map_add_const

/-- **Piece 2 of Robbin's Lemma 4.3: the flux as the log-coefficient of the circle means.**

For `V` harmonic on the plane annulus `ρ < ‖z - a‖ < R`, the rearrangement of the (green) annulus
lemma `Work.Drive.circleFlux_eq_of_harmonicOn_annulus` solving for the flux:

`circleFlux V a r = 2 * π * (circleAverage V a r' - circleAverage V a r) / Real.log (r' / r)`.

This is the form the Liouville argument consumes: the right-hand side is a difference of circle means
of the harmonic function, uniformly bounded by the maximum principle, divided by `Real.log (r'/r)`.
-/
theorem circleFlux_eq_of_mean_diff {V : ℂ → ℝ} {a : ℂ} {ρ R r r' : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hV : ∀ z : ℂ, ρ < ‖z - a‖ → ‖z - a‖ < R → InnerProductSpace.HarmonicAt V z)
    (hr : ρ < r) (hrR : r < R) (hr' : ρ < r') (hr'R : r' < R) (hrr' : r < r') :
    Work.Drive.circleFlux V a r
      = 2 * Real.pi * (Real.circleAverage V a r' - Real.circleAverage V a r)
          / Real.log (r' / r) := by
  have h := Work.Drive.circleFlux_eq_of_harmonicOn_annulus (V := V) (a := a)
    hρ hρR hV hr hrR hr' hr'R
  have hr0 : 0 < r := lt_trans hρ hr
  have hr'0 : 0 < r' := lt_trans hρ hr'
  have hne : r' / r ≠ 1 := by
    intro h1
    exact absurd ((div_eq_one_iff_eq (ne_of_gt hr0)).mp h1) (ne_of_gt hrr')
  have hlog : Real.log (r' / r) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (div_pos hr'0 hr0) hne
  rw [h]
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp

/-- **Piece 3 of Robbin's Lemma 4.3: the Liouville step (corrected form).**

Let `v : X → ℝ` be the limit of the solutions of the Dirichlet problem on `Ωₙ` (data `1` near the
chart sphere, `0` near `∂Xₙ`), so that `0 ≤ v ≤ 1`, `1 - v` is harmonic where it is positive, and
`1 - v ≡ 0` inside the chart ball.  Then `hLiou` forces `v ≡ 1`.

The zero-extension argument runs on `1 - v` itself, **not** on `1 - vₙ` (see `HANDOFF.md` ADDENDUM 5s).
-/
theorem eq_one_of_subharmonic_zeroExtension {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hLiou : ∀ w : X → ℝ, Submission.SubharmonicOnX w Set.univ →
      (∃ M : ℝ, ∀ x : X, w x ≤ M) → ∀ x y : X, w x = w y)
    {v : X → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1)
    (hcont : Continuous (fun x => 1 - v x))
    (hharm : Submission.HarmonicOnX (fun x => 1 - v x) {x : X | 0 < 1 - v x})
    (hvanish : ∃ x, v x = 1) :
    ∀ x, v x = 1 := by
  set u : X → ℝ := fun x => 1 - v x with hu
  have hnn : ∀ x, 0 ≤ u x := fun x => by
    have := hv1 x; simp only [hu]; linarith
  have hbdd : ∀ x, u x ≤ 1 := fun x => by
    have := hv0 x; simp only [hu]; linarith
  have hzero : ∀ x ∉ {x : X | 0 < u x}, u x = 0 := fun x hx => by
    have h2 : ¬ (0 < u x) := hx
    have h3 := hnn x
    simp only [not_lt] at h2
    linarith
  have hsub : Submission.SubharmonicOnX u Set.univ :=
    SubharmonicOnX.of_nonneg_harmonic_zeroExtension (isOpen_lt continuous_const hcont) hcont
      hnn hzero (by simpa only [hu] using hharm)
  have hconst : ∀ x y : X, u x = u y := hLiou u hsub ⟨1, hbdd⟩
  obtain ⟨x₀, hx₀⟩ := hvanish
  intro x
  have h0 : u x₀ = 0 := by simp only [hu]; linarith
  have hx0 : u x = 0 := by rw [hconst x x₀, h0]
  simp only [hu] at hx0
  linarith

end Model

end Work.Drive
