import Mathlib
import Submission.Lib.Unif2.Work.Drive.ChartFlux
import Submission.Lib.Unif2.Work.Potential.harmonic_annulus_fourier_structure
import Submission.Lib.Unif2.Work.Potential.log_estimate_defs
import Submission.Lib.Unif2.Work.Potential.strip_integral_hasDerivAt
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

/-!
# The circle flux of a harmonic function on an annulus

For a function `V : ℂ → ℝ` harmonic on the annulus `ρ < ‖z - a‖ < R`, the circle means
`r ↦ Real.circleAverage V a r` are affine in `log r`, and the slope is (twice `π` times) the flux
`Work.Drive.circleFlux V a r` through any circle of the annulus.  Consequently
`circleAverage V a r' - circleAverage V a r = circleFlux V a r * log (r' / r) / (2 * π)`.

The proof reduces to the centre `0` by translation, then lifts `V` to the vertical strip
`{log ρ < re w < log R}` by `w ↦ V (exp w)`.  The Fourier-free part of
`Work.Potential.harmonic_annulus_fourier_structure` gives the affine structure of the mean, and
`Work.Potential.strip_integral_hasDerivAt` computes the derivative of the strip integral: its real
part is (up to `2π`) the flux, and comparing with the slope of the affine mean identifies the two.
-/

open Complex MeasureTheory Filter Set
open scoped Topology Interval

namespace Work.Drive

/-- The radial derivative is the derivative in the radial direction: for `V` differentiable at `z`
it is `fderiv ℝ V z (z - a)`. -/
theorem radialDeriv_eq_fderiv {V : ℂ → ℝ} {a z : ℂ} (hV : DifferentiableAt ℝ V z) :
    radialDeriv V a z = fderiv ℝ V z (z - a) := by
  have hγ : HasDerivAt (fun t : ℝ => a + (t : ℂ) * (z - a)) (z - a) 1 := by
    have h := (hasDerivAt_id (1 : ℝ)).ofReal_comp.mul_const (z - a)
    have h2 := h.const_add a
    simpa using h2
  have hV' : DifferentiableAt ℝ V ((fun t : ℝ => a + (t : ℂ) * (z - a)) 1) := by
    simpa using hV
  have hcomp := hV'.hasFDerivAt.comp_hasDerivAt 1 hγ
  have h1 : deriv (fun t : ℝ => V (a + (t : ℂ) * (z - a))) 1
      = fderiv ℝ V ((fun t : ℝ => a + (t : ℂ) * (z - a)) 1) (z - a) := by
    simpa [Function.comp_def] using hcomp.deriv
  rw [radialDeriv, h1]
  congr 1
  simp

/-- The flux is invariant under translating the centre to the origin. -/
theorem circleFlux_map_add_const (V : ℂ → ℝ) (a : ℂ) (r : ℝ) :
    circleFlux (fun z : ℂ => V (z + a)) 0 r = circleFlux V a r := by
  have hpt : (fun z : ℂ => radialDeriv (fun w : ℂ => V (w + a)) 0 z)
      = fun z : ℂ => radialDeriv V a (z + a) := by
    funext z
    simp only [radialDeriv]
    congr 1
    funext t
    congr 1
    ring
  simp only [circleFlux]
  rw [hpt, Real.circleAverage_map_add_const]

/-- **The real derivative of the exponential lift.**  For `V` differentiable at `exp w`, the
derivative of the complex-valued lift `w ↦ V (exp w)` in the real direction `1` has real part the
radial derivative of `V` at `exp w`. -/
theorem re_fderiv_expLift {V : ℂ → ℝ} {w : ℂ} (hV : DifferentiableAt ℝ V (Complex.exp w)) :
    (fderiv ℝ (Work.Potential.expLift V) w 1).re = radialDeriv V 0 (Complex.exp w) := by
  have hexp : DifferentiableAt ℝ Complex.exp w := by fun_prop
  have hU : DifferentiableAt ℝ (fun u : ℂ => V (Complex.exp u)) w := hV.comp w hexp
  have hfac : fderiv ℝ (Work.Potential.expLift V) w
      = Complex.ofRealCLM.comp (fderiv ℝ (fun u : ℂ => V (Complex.exp u)) w) := by
    rw [show Work.Potential.expLift V
        = Complex.ofRealCLM ∘ (fun u : ℂ => V (Complex.exp u)) from rfl]
    rw [fderiv_comp w Complex.ofRealCLM.differentiableAt hU, ContinuousLinearMap.fderiv]
  have hval : fderiv ℝ (Work.Potential.expLift V) w 1
      = ((fderiv ℝ (fun u : ℂ => V (Complex.exp u)) w 1 : ℝ) : ℂ) := by
    rw [hfac, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  have hU1 : fderiv ℝ (fun u : ℂ => V (Complex.exp u)) w 1
      = fderiv ℝ V (Complex.exp w) ((fderiv ℝ Complex.exp w) 1) := by
    change fderiv ℝ (V ∘ Complex.exp) w 1
      = fderiv ℝ V (Complex.exp w) ((fderiv ℝ Complex.exp w) 1)
    rw [fderiv_comp w hV hexp, ContinuousLinearMap.comp_apply]
  have hexp1 : (fderiv ℝ Complex.exp w) 1 = Complex.exp w := by
    have h := (Complex.hasDerivAt_exp w).hasFDerivAt.restrictScalars ℝ
    rw [h.fderiv]
    show (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp w)) 1 = Complex.exp w
    simp
  rw [hval, Complex.ofReal_re, hU1, hexp1, radialDeriv_eq_fderiv (a := 0) hV, sub_zero]

/-- **The flux is `2π` times the slope of the mean.**  If the circle means of a function harmonic
on the annulus `ρ < ‖z‖ < R` are `α + β log r`, then the flux through every circle of the annulus
is `2π β`. -/
theorem circleFlux_eq_two_pi_mul_slope {V : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hV : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt V z)
    {α β : ℝ} (hmean : ∀ r : ℝ, ρ < r → r < R → Real.circleAverage V 0 r = α + β * Real.log r)
    {r : ℝ} (hr : ρ < r) (hrR : r < R) : circleFlux V 0 r = 2 * Real.pi * β := by
  have hrpos : 0 < r := lt_trans hρ hr
  set s₀ : ℝ := Real.log r with hs₀
  have hlogr : Real.exp s₀ = r := by rw [hs₀]; exact Real.exp_log hrpos
  have hs₁ : Real.log ρ < s₀ := by rw [hs₀]; exact Real.log_lt_log hρ hr
  have hs₂ : s₀ < Real.log R := by rw [hs₀]; exact Real.log_lt_log hrpos hrR
  have hsl₁ : ∀ θ : ℝ, Real.log ρ < ((s₀ : ℂ) + (θ : ℂ) * Complex.I).re := by
    intro θ; rw [show ((s₀ : ℂ) + (θ : ℂ) * Complex.I).re = s₀ from by simp]; exact hs₁
  have hsl₂ : ∀ θ : ℝ, ((s₀ : ℂ) + (θ : ℂ) * Complex.I).re < Real.log R := by
    intro θ; rw [show ((s₀ : ℂ) + (θ : ℂ) * Complex.I).re = s₀ from by simp]; exact hs₂
  -- the mean, as an integral, is affine near `s₀`
  have hint : (fun s : ℝ => (∫ θ in (0:ℝ)..(2 * Real.pi),
        Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)).re)
      =ᶠ[𝓝 s₀] fun s : ℝ => 2 * Real.pi * (α + β * s) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show s₀ ∈ Set.Ioo (Real.log ρ) (Real.log R) from ⟨hs₁, hs₂⟩)] with s hs
    obtain ⟨hs₁', hs₂'⟩ := hs
    have hes₁ : ρ < Real.exp s := by rw [← Real.exp_log hρ]; exact Real.exp_lt_exp.mpr hs₁'
    have hes₂ : Real.exp s < R := by
      rw [← Real.exp_log (lt_trans hρ hρR)]; exact Real.exp_lt_exp.mpr hs₂'
    have hint' : IntervalIntegrable
        (fun θ : ℝ => Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)) volume
        (0 : ℝ) (2 * Real.pi) := by
      apply ContinuousOn.intervalIntegrable
      intro θ _
      have hw₁ : Real.log ρ < ((s : ℂ) + (θ : ℂ) * Complex.I).re := by
        rw [show ((s : ℂ) + (θ : ℂ) * Complex.I).re = s from by simp]; exact hs₁'
      have hw₂ : ((s : ℂ) + (θ : ℂ) * Complex.I).re < Real.log R := by
        rw [show ((s : ℂ) + (θ : ℂ) * Complex.I).re = s from by simp]; exact hs₂'
      have hAt : ContinuousAt (Work.Potential.expLift V) ((s : ℂ) + (θ : ℂ) * Complex.I) :=
        (Work.Potential.contDiffAt_expLift hρ hρR hV (n := 2) hw₁ hw₂).continuousAt
      have hlin : ContinuousAt (fun θ' : ℝ => (s : ℂ) + (θ' : ℂ) * Complex.I) θ := by fun_prop
      exact (ContinuousAt.comp' (x := θ)
        (f := fun θ' : ℝ => (s : ℂ) + (θ' : ℂ) * Complex.I) hAt hlin).continuousWithinAt
    have hre := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (a := (0:ℝ))
      (b := 2 * Real.pi) hint'
    simp only [Complex.reCLM_apply] at hre
    rw [← hre]
    have hpt : (∫ θ in (0:ℝ)..(2 * Real.pi),
          (Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)).re)
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            V (Real.exp s * Complex.exp (θ * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only []
      have h1 : Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)
          = ((V (Real.exp s * Complex.exp (θ * Complex.I)) : ℝ) : ℂ) := by
        show ((V (Complex.exp ((s : ℂ) + (θ : ℂ) * Complex.I)) : ℝ) : ℂ) = _
        rw [Complex.exp_add, ← Complex.ofReal_exp]
      rw [h1, Complex.ofReal_re]
    rw [hpt]
    change Work.Potential.angMean V (Real.exp s) = 2 * Real.pi * (α + β * s)
    rw [Work.Potential.angMean_eq V (Real.exp s), hmean (Real.exp s) hes₁ hes₂, Real.log_exp]
  -- the strip integral and its derivative
  have hderiv := Work.Potential.strip_integral_hasDerivAt (f := Work.Potential.expLift V)
    (δ₁ := Real.log ρ) (δ₂ := Real.log R) (k := 0) (s₀ := s₀) hs₁ hs₂
    (fun w hw₁ hw₂ => Work.Potential.contDiffAt_expLift hρ hρR hV (n := 2) hw₁ hw₂)
  have hfun : (fun s : ℝ => ∫ θ in (0:ℝ)..(2 * Real.pi),
        Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)
          * Complex.exp (-((((0:ℤ):ℝ):ℂ) * (θ:ℂ) * Complex.I)))
      = fun s : ℝ => ∫ θ in (0:ℝ)..(2 * Real.pi),
          Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I) := by
    funext s
    apply intervalIntegral.integral_congr
    intro θ _
    simp
  have hval_eq : (∫ θ in (0:ℝ)..(2 * Real.pi),
        (fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) 1
          * Complex.exp (-((((0:ℤ):ℝ):ℂ) * (θ:ℂ) * Complex.I)))
      = ∫ θ in (0:ℝ)..(2 * Real.pi),
          (fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) 1 := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp
  rw [hfun, hval_eq] at hderiv
  -- take real parts
  have hderiv_re : HasDerivAt (fun s : ℝ => (∫ θ in (0:ℝ)..(2 * Real.pi),
        Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)).re)
      ((∫ θ in (0:ℝ)..(2 * Real.pi),
        (fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) 1).re) s₀ := by
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s₀ hderiv
    simpa [Function.comp_def, Complex.reCLM_apply] using h2
  -- the derivative of the affine function
  have haff : HasDerivAt (fun s : ℝ => 2 * Real.pi * (α + β * s)) (2 * Real.pi * β) s₀ := by
    have h : HasDerivAt (fun s : ℝ => α + β * s) β s₀ := by
      simpa using ((hasDerivAt_id s₀).const_mul β).const_add α
    exact h.const_mul (2 * Real.pi)
  have h1 : HasDerivAt (fun s : ℝ => (∫ θ in (0:ℝ)..(2 * Real.pi),
        Work.Potential.expLift V ((s : ℂ) + (θ : ℂ) * Complex.I)).re) (2 * Real.pi * β) s₀ :=
    haff.congr_of_eventuallyEq hint
  have hfl : (∫ θ in (0:ℝ)..(2 * Real.pi),
        (fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) 1).re
      = 2 * Real.pi * β := (h1.unique hderiv_re).symm
  -- the derivative integrand is continuous, hence interval integrable
  have hcontDeriv : Continuous (fun θ : ℝ =>
      fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hAt := (Work.Potential.contDiffAt_expLift hρ hρR hV (n := 2) (hsl₁ θ) (hsl₂ θ)
      ).continuousAt_fderiv (by norm_num)
    have hlin : ContinuousAt (fun θ' : ℝ => (s₀ : ℂ) + (θ' : ℂ) * Complex.I) θ := by fun_prop
    exact ContinuousAt.comp' (x := θ)
      (f := fun θ' : ℝ => (s₀ : ℂ) + (θ' : ℂ) * Complex.I) hAt hlin
  have hint2 : IntervalIntegrable (fun θ : ℝ =>
      (fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) 1) volume
      (0 : ℝ) (2 * Real.pi) :=
    (hcontDeriv.clm_apply (continuous_const (y := (1 : ℂ)))).intervalIntegrable 0 (2 * Real.pi)
  have hre2 := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (a := (0:ℝ))
    (b := 2 * Real.pi) hint2
  simp only [Complex.reCLM_apply] at hre2
  -- the integrand is the radial derivative along the circle of radius `r`
  have hpt2 : (∫ θ in (0:ℝ)..(2 * Real.pi),
        ((fderiv ℝ (Work.Potential.expLift V) ((s₀ : ℂ) + (θ : ℂ) * Complex.I)) 1).re)
      = ∫ θ in (0:ℝ)..(2 * Real.pi), radialDeriv V 0 (r * Complex.exp (θ * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only []
    have hw₁ : ρ < ‖Complex.exp ((s₀ : ℂ) + (θ : ℂ) * Complex.I)‖ := by
      rw [Complex.norm_exp]
      rw [show ((s₀ : ℂ) + (θ : ℂ) * Complex.I).re = s₀ from by simp, hlogr]; exact hr
    have hw₂ : ‖Complex.exp ((s₀ : ℂ) + (θ : ℂ) * Complex.I)‖ < R := by
      rw [Complex.norm_exp]
      rw [show ((s₀ : ℂ) + (θ : ℂ) * Complex.I).re = s₀ from by simp, hlogr]; exact hrR
    have hexp : Complex.exp ((s₀ : ℂ) + (θ : ℂ) * Complex.I)
        = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, hlogr]
    rw [re_fderiv_expLift ((hV _ hw₁ hw₂).1.differentiableAt (by norm_num)), hexp]
  -- the flux is the angular integral of the radial derivative
  have hflux : circleFlux V 0 r
      = ∫ θ in (0:ℝ)..(2 * Real.pi), radialDeriv V 0 (r * Complex.exp (θ * Complex.I)) := by
    have h := Work.Potential.angMean_eq (fun z : ℂ => radialDeriv V 0 z) r
    rw [circleFlux, ← h]
    rfl
  rw [hflux, ← hpt2, hre2, hfl]

/-- **The logarithmic mean value formula, centre `0`.**  The difference of the circle means of a
harmonic function on an annulus is the flux times `log (r' / r) / (2π)`. -/
theorem circleAverage_sub_eq_flux_mul_log_zero {V : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hV : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt V z)
    {r r' : ℝ} (hr : ρ < r) (hrR : r < R) (hr' : ρ < r') (hr'R : r' < R) :
    Real.circleAverage V 0 r' - Real.circleAverage V 0 r
      = circleFlux V 0 r * Real.log (r' / r) / (2 * Real.pi) := by
  obtain ⟨hcoeff, -⟩ := Work.Potential.harmonic_annulus_fourier_structure hρ hρR hV
  obtain ⟨α, β, hαβ⟩ := hcoeff
  have hmean : ∀ s : ℝ, ρ < s → s < R → Real.circleAverage V 0 s = α + β * Real.log s := by
    intro s hs₁ hs₂
    have h := hαβ s hs₁ hs₂
    have h2 := Work.Potential.angMean_eq V s
    simp only [Work.Potential.angMean] at h2
    rw [h] at h2
    exact (mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0) h2).symm
  have hflux := circleFlux_eq_two_pi_mul_slope hρ hρR hV hmean hr hrR
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [hmean r' hr' hr'R, hmean r hr hrR, hflux,
    Real.log_div (ne_of_gt (lt_trans hρ hr')) (ne_of_gt (lt_trans hρ hr))]
  field_simp
  ring

/-- **The logarithmic mean value formula for a harmonic function on an annulus.**  For `V` harmonic
on `{z | ρ < ‖z - a‖ < R}` and `ρ < r, r' < R`, the difference of the circle means about `a` is the
flux through the circle of radius `r` times `log (r' / r) / (2π)`. -/
theorem circleFlux_eq_of_harmonicOn_annulus {V : ℂ → ℝ} {a : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hV : ∀ z : ℂ, ρ < ‖z - a‖ → ‖z - a‖ < R → InnerProductSpace.HarmonicAt V z)
    {r r' : ℝ} (hr : ρ < r) (hrR : r < R) (hr' : ρ < r') (hr'R : r' < R) :
    Real.circleAverage V a r' - Real.circleAverage V a r
      = (Work.Drive.circleFlux V a r) * Real.log (r' / r) / (2 * Real.pi) := by
  set W : ℂ → ℝ := fun z => V (z + a) with hW
  have hWharm : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt W z := by
    intro z hz1 hz2
    have h1 : ρ < ‖z + a - a‖ := by rw [add_sub_cancel_right]; exact hz1
    have h2 : ‖z + a - a‖ < R := by rw [add_sub_cancel_right]; exact hz2
    have hf : AnalyticAt ℂ (fun z : ℂ => z + a) z :=
      analyticAt_id.add (analyticAt_const (v := a))
    have hcomp := Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic hf (hV (z + a) h1 h2)
    simpa [Function.comp, W] using hcomp
  have hmain := circleAverage_sub_eq_flux_mul_log_zero hρ hρR hWharm hr hrR hr' hr'R
  rw [show Work.Drive.circleFlux W 0 r = Work.Drive.circleFlux V a r from by
        rw [hW]; exact circleFlux_map_add_const V a r,
      show Real.circleAverage W 0 r' = Real.circleAverage V a r' from by
        rw [hW]; exact Real.circleAverage_map_add_const,
      show Real.circleAverage W 0 r = Real.circleAverage V a r from by
        rw [hW]; exact Real.circleAverage_map_add_const] at hmain
  exact hmain

end Work.Drive
