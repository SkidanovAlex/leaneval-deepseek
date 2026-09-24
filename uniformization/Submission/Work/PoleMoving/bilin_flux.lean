import Mathlib
import Submission.Work.Drive.ChartFlux
import Submission.Work.Drive.circleFlux_eq_of_harmonicOn_annulus

/-!
# The bilinear period (Green) identity on an annulus, in verified form

Promoted from `Scratch/bilin_flux_dev.lean` (sorry-free there) so that the flux/period arguments
can cite it: `Work.Drive.circleAverage_bilin_zero_eq` is the period identity
`circleAverage (v ∂ᵣu − u ∂ᵣv) 0 r = circleAverage (v ∂ᵣu − u ∂ᵣv) 0 r'` for `u`, `v` harmonic on the
open annulus `{ρ < ‖z‖ < R}` and *interior* radii `ρ < r, r' < R`, i.e. the classical Green identity
`∮ (v ∂ₙu − u ∂ₙv) ds` on two concentric circles, obtained Stokes-free by the exponential-strip lift.
`Work.Drive.circleFluxBilin_eq_of_harmonicOn_annulus` is the corresponding flux form.

## CONVENTION (learned the hard way — apply to every period/pairing statement)

**The harmonicity domain must contain a *neighbourhood of the curve you integrate over*, never
merely its interior side.**  A pairing statement whose hypotheses bind `a`, `b` only on the open
region *inside* the curve compares quantities that the hypotheses leave free on the curve itself,
and is false.  This has bitten twice:
* the concentric circle pairing: harmonicity on `ρ < ‖z‖ < R` does not constrain the boundary
  circles `‖z‖ = ρ`, `R` (take `v ≡ 1`, `u = log‖z‖` inside `R` and `0` outside: `1` vs `0`); hence
  the verified `circleAverage_bilin_zero_eq` requires *interior* radii `ρ < r, r' < R`;
* the two-disjoint-circles pairing: harmonicity on the open annulus
  `ball q σ ∖ closedBall p ρ` does not constrain `S(q,σ)` or `S(p,ρ)` (take the concentric case
  `b ≡ 1`, `a = log‖z‖`; inner average `1`, outer `0`).

The fix in both cases: assume harmonicity on a strictly *larger* region,
`ρ' < ρ < σ < σ'` in the two-circle case, so that `closure U` sits in the harmonicity domain.  This
is also exactly the `C¹`-on-`closure U` side condition the divergence-theorem route needs.
The same applies to *differentiability*: `fderiv ℝ f z` is junk (`0`) wherever `f` is not
differentiable at `z`, so any statement comparing `fderiv` with `Work.Drive.radialDeriv` must assume
differentiability at each point of the curve (`radialDeriv_eq_fderiv` carries exactly that
hypothesis).  A kink along the curve is enough to break the comparison (`a ≡ 1`, `b` with a kink on
the circle: the `fderiv` integrand vanishes identically while `∫ radialDeriv b` does not).

Conventions (both corrected by review): `Work.Drive.radialDeriv` is the *unnormalised* directional
derivative, so on `‖z‖ = r` it already carries the factor `r`, and `Real.circleAverage` is a
θ-average; hence `2π · circleAverage F 0 r = ∮_{‖z‖=r}(v ∂ₙu − u ∂ₙv) ds` with no extra radius
factor (with `u ≡ 1`, `v = log‖z‖` one has `F ≡ 1`).  The radii must be interior: on the boundary
radii the hypotheses constrain nothing (`v ≡ 1` with `u = log‖z‖` inside `R` and `0` outside).
-/

noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology Interval

namespace Work.Drive

/-- The complex lift of the bilinear flux integrand to the logarithmic strip:
`w ↦ v(exp w) ∂_s u(exp w) - u(exp w) ∂_s v(exp w)`. -/
def bilinStrip (u v : ℂ → ℝ) : ℂ → ℂ := fun w =>
  Work.Potential.expLift v w * Work.Potential.dS (Work.Potential.expLift u) w
    - Work.Potential.expLift u w * Work.Potential.dS (Work.Potential.expLift v) w

lemma radialDeriv_map_add_const (u : ℂ → ℝ) (a z : ℂ) :
    radialDeriv (fun w : ℂ => u (w + a)) 0 z = radialDeriv u a (z + a) := by
  simp only [radialDeriv]
  congr 1
  funext t
  congr 1
  ring

lemma contDiffAt_bilinStrip {u v : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    {w : ℂ} (hw₁ : Real.log ρ < w.re) (hw₂ : w.re < Real.log R) :
    ContDiffAt ℝ 2 (bilinStrip u v) w := by
  have hU : ContDiffAt ℝ 2 (Work.Potential.expLift u) w :=
    Work.Potential.contDiffAt_expLift hρ hρR hu hw₁ hw₂
  have hV : ContDiffAt ℝ 2 (Work.Potential.expLift v) w :=
    Work.Potential.contDiffAt_expLift hρ hρR hv hw₁ hw₂
  have hdU : ContDiffAt ℝ 2 (Work.Potential.dS (Work.Potential.expLift u)) w :=
    Work.Potential.contDiffAt_dS hρ hρR hu (n := 2) hw₁ hw₂
  have hdV : ContDiffAt ℝ 2 (Work.Potential.dS (Work.Potential.expLift v)) w :=
    Work.Potential.contDiffAt_dS hρ hρR hv (n := 2) hw₁ hw₂
  have h : ContDiffAt ℝ 2 (Work.Potential.expLift v * Work.Potential.dS (Work.Potential.expLift u)
      - Work.Potential.expLift u * Work.Potential.dS (Work.Potential.expLift v)) w :=
    (hV.mul hdU).sub (hU.mul hdV)
  change ContDiffAt ℝ 2 (fun w : ℂ => Work.Potential.expLift v w
      * Work.Potential.dS (Work.Potential.expLift u) w
      - Work.Potential.expLift u w * Work.Potential.dS (Work.Potential.expLift v) w) w
  exact h

lemma fderiv_bilinStrip {u v : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    {w : ℂ} (hw₁ : Real.log ρ < w.re) (hw₂ : w.re < Real.log R) :
    fderiv ℝ (bilinStrip u v) w 1
      = Work.Potential.expLift v w * Work.Potential.dS (Work.Potential.dS (Work.Potential.expLift u)) w
        - Work.Potential.expLift u w * Work.Potential.dS (Work.Potential.dS (Work.Potential.expLift v)) w := by
  have hU : DifferentiableAt ℝ (Work.Potential.expLift u) w :=
    (Work.Potential.contDiffAt_expLift hρ hρR hu (n := 1) hw₁ hw₂).differentiableAt (by norm_num)
  have hV : DifferentiableAt ℝ (Work.Potential.expLift v) w :=
    (Work.Potential.contDiffAt_expLift hρ hρR hv (n := 1) hw₁ hw₂).differentiableAt (by norm_num)
  have hdU : DifferentiableAt ℝ (Work.Potential.dS (Work.Potential.expLift u)) w :=
    (Work.Potential.contDiffAt_dS hρ hρR hu (n := 1) hw₁ hw₂).differentiableAt (by norm_num)
  have hdV : DifferentiableAt ℝ (Work.Potential.dS (Work.Potential.expLift v)) w :=
    (Work.Potential.contDiffAt_dS hρ hρR hv (n := 1) hw₁ hw₂).differentiableAt (by norm_num)
  have hsub : fderiv ℝ (bilinStrip u v) w
      = fderiv ℝ (Work.Potential.expLift v * Work.Potential.dS (Work.Potential.expLift u)) w
        - fderiv ℝ (Work.Potential.expLift u * Work.Potential.dS (Work.Potential.expLift v)) w := by
    rw [show bilinStrip u v
        = Work.Potential.expLift v * Work.Potential.dS (Work.Potential.expLift u)
          - Work.Potential.expLift u * Work.Potential.dS (Work.Potential.expLift v) from rfl]
    exact fderiv_sub (hV.mul hdU) (hU.mul hdV)
  rw [hsub, fderiv_mul hV hdU, fderiv_mul hU hdV]
  simp [Work.Potential.dS]
  ring

/-- The primitive in `θ` (along a vertical line of the strip) of the bilinear strip integrand. -/
def bilinPrim (u v : ℂ → ℝ) (s : ℝ) : ℝ → ℂ := fun θ =>
  Work.Potential.expLift v ((s:ℂ) + (θ:ℂ)*Complex.I)
      * Work.Potential.dI (Work.Potential.expLift u) ((s:ℂ) + (θ:ℂ)*Complex.I)
    - Work.Potential.expLift u ((s:ℂ) + (θ:ℂ)*Complex.I)
      * Work.Potential.dI (Work.Potential.expLift v) ((s:ℂ) + (θ:ℂ)*Complex.I)

/-- Its `θ`-derivative. -/
def bilinPrimDeriv (u v : ℂ → ℝ) (s : ℝ) : ℝ → ℂ := fun θ =>
  Work.Potential.expLift v ((s:ℂ) + (θ:ℂ)*Complex.I)
      * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift u)) ((s:ℂ) + (θ:ℂ)*Complex.I)
    - Work.Potential.expLift u ((s:ℂ) + (θ:ℂ)*Complex.I)
      * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift v)) ((s:ℂ) + (θ:ℂ)*Complex.I)

lemma hasDerivAt_bilinPrim {u v : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    {s : ℝ} (hs₁ : Real.log ρ < s) (hs₂ : s < Real.log R) (θ : ℝ) :
    HasDerivAt (bilinPrim u v s) (bilinPrimDeriv u v s θ) θ := by
  have h1 := (Work.Potential.hasDerivAt_expLift_line hρ hρR hv hs₁ hs₂ θ).mul
    (Work.Potential.hasDerivAt_dI_expLift_line hρ hρR hu hs₁ hs₂ θ)
  have h2 := (Work.Potential.hasDerivAt_expLift_line hρ hρR hu hs₁ hs₂ θ).mul
    (Work.Potential.hasDerivAt_dI_expLift_line hρ hρR hv hs₁ hs₂ θ)
  have h := h1.sub h2
  have hfun : ((fun θ : ℝ => Work.Potential.expLift v ((s:ℂ) + (θ:ℂ)*Complex.I))
        * (fun θ : ℝ => Work.Potential.dI (Work.Potential.expLift u) ((s:ℂ) + (θ:ℂ)*Complex.I))
      - (fun θ : ℝ => Work.Potential.expLift u ((s:ℂ) + (θ:ℂ)*Complex.I))
        * (fun θ : ℝ => Work.Potential.dI (Work.Potential.expLift v) ((s:ℂ) + (θ:ℂ)*Complex.I)))
      = fun t : ℝ => Work.Potential.expLift v ((s:ℂ) + (t:ℂ)*Complex.I)
          * Work.Potential.dI (Work.Potential.expLift u) ((s:ℂ) + (t:ℂ)*Complex.I)
        - Work.Potential.expLift u ((s:ℂ) + (t:ℂ)*Complex.I)
          * Work.Potential.dI (Work.Potential.expLift v) ((s:ℂ) + (t:ℂ)*Complex.I) := rfl
  have hval : (Work.Potential.dI (Work.Potential.expLift v) ((s:ℂ) + (θ:ℂ)*Complex.I)
        * Work.Potential.dI (Work.Potential.expLift u) ((s:ℂ) + (θ:ℂ)*Complex.I)
      + Work.Potential.expLift v ((s:ℂ) + (θ:ℂ)*Complex.I)
        * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift u)) ((s:ℂ) + (θ:ℂ)*Complex.I))
      - (Work.Potential.dI (Work.Potential.expLift u) ((s:ℂ) + (θ:ℂ)*Complex.I)
          * Work.Potential.dI (Work.Potential.expLift v) ((s:ℂ) + (θ:ℂ)*Complex.I)
        + Work.Potential.expLift u ((s:ℂ) + (θ:ℂ)*Complex.I)
          * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift v)) ((s:ℂ) + (θ:ℂ)*Complex.I))
      = Work.Potential.expLift v ((s:ℂ) + (θ:ℂ)*Complex.I)
          * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift u)) ((s:ℂ) + (θ:ℂ)*Complex.I)
        - Work.Potential.expLift u ((s:ℂ) + (θ:ℂ)*Complex.I)
          * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift v)) ((s:ℂ) + (θ:ℂ)*Complex.I) := by
    ring
  rw [hfun] at h
  rw [hval] at h
  change HasDerivAt (bilinPrim u v s) (bilinPrimDeriv u v s θ) θ
  exact h

lemma bilinPrim_two_pi {u v : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    {s : ℝ} (hs₁ : Real.log ρ < s) (hs₂ : s < Real.log R) :
    bilinPrim u v s (2 * Real.pi) = bilinPrim u v s 0 := by
  have h1 : (s : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (s : ℂ) + 2 * Real.pi * Complex.I := by push_cast; ring
  have h2 : (s : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = (s : ℂ) := by push_cast; ring
  have hV := Work.Potential.expLift_add_two_pi v (s : ℂ)
  have hU := Work.Potential.expLift_add_two_pi u (s : ℂ)
  have hdV := Work.Potential.fderiv_expLift_add_two_pi (u := v) hρ hρR hv (w := (s:ℂ))
    (by simpa using hs₁) (by simpa using hs₂)
  have hdU := Work.Potential.fderiv_expLift_add_two_pi (u := u) hρ hρR hu (w := (s:ℂ))
    (by simpa using hs₁) (by simpa using hs₂)
  simp only [bilinPrim]
  rw [h1, h2]
  simp only [Work.Potential.dI]
  rw [hV, hU, hdV, hdU]

lemma continuous_expLift_line {u : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    {s : ℝ} (hs₁ : Real.log ρ < s) (hs₂ : s < Real.log R) :
    Continuous (fun θ : ℝ => Work.Potential.expLift u ((s:ℂ) + (θ:ℂ)*Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun θ => ?_
  have hw₁ : Real.log ρ < ((s:ℂ) + (θ:ℂ)*Complex.I).re := by
    rw [Work.Potential.line_re]; exact hs₁
  have hw₂ : ((s:ℂ) + (θ:ℂ)*Complex.I).re < Real.log R := by
    rw [Work.Potential.line_re]; exact hs₂
  exact ContinuousAt.comp' (x := θ) (f := fun θ : ℝ => (s:ℂ) + (θ:ℂ)*Complex.I)
    (Work.Potential.contDiffAt_expLift hρ hρR hu (n := 1) hw₁ hw₂).continuousAt (by fun_prop)

lemma continuous_dIdI_line {u : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    {s : ℝ} (hs₁ : Real.log ρ < s) (hs₂ : s < Real.log R) :
    Continuous (fun θ : ℝ => Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift u))
      ((s:ℂ) + (θ:ℂ)*Complex.I)) := by
  have h0 : Continuous (fun θ : ℝ => fderiv ℝ (Work.Potential.dI (Work.Potential.expLift u))
      ((s:ℂ) + (θ:ℂ)*Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hw₁ : Real.log ρ < ((s:ℂ) + (θ:ℂ)*Complex.I).re := by
      rw [Work.Potential.line_re]; exact hs₁
    have hw₂ : ((s:ℂ) + (θ:ℂ)*Complex.I).re < Real.log R := by
      rw [Work.Potential.line_re]; exact hs₂
    exact ContinuousAt.comp' (x := θ) (f := fun θ : ℝ => (s:ℂ) + (θ:ℂ)*Complex.I)
      ((Work.Potential.contDiffAt_dI hρ hρR hu (n := 2) hw₁ hw₂).continuousAt_fderiv
        (by norm_num)) (by fun_prop)
  simpa only [Work.Potential.dI] using h0.clm_apply continuous_const

lemma hasDerivAt_bilinStrip_integral {u v : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    {s₀ : ℝ} (hs₁ : Real.log ρ < s₀) (hs₂ : s₀ < Real.log R) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0:ℝ)..(2*Real.pi),
        bilinStrip u v ((s:ℂ) + (θ:ℂ)*Complex.I)) 0 s₀ := by
  have hΨ2 : ∀ w : ℂ, Real.log ρ < w.re → w.re < Real.log R →
      ContDiffAt ℝ 2 (bilinStrip u v) w :=
    fun w hw₁ hw₂ => contDiffAt_bilinStrip hρ hρR hu hv hw₁ hw₂
  have hd : HasDerivAt
      (fun s : ℝ => ∫ θ in (0:ℝ)..(2*Real.pi), bilinStrip u v ((s:ℂ) + (θ:ℂ)*Complex.I))
      (∫ θ in (0:ℝ)..(2*Real.pi), fderiv ℝ (bilinStrip u v) ((s₀:ℂ) + (θ:ℂ)*Complex.I) 1) s₀ := by
    simpa using Work.Potential.strip_integral_hasDerivAt (f := bilinStrip u v) (δ₁ := Real.log ρ)
      (δ₂ := Real.log R) (k := 0) hs₁ hs₂ hΨ2
  have hpoint : ∀ θ : ℝ, fderiv ℝ (bilinStrip u v) ((s₀:ℂ) + (θ:ℂ)*Complex.I) 1
      = - (bilinPrimDeriv u v s₀ θ) := by
    intro θ
    have hw₁ : Real.log ρ < ((s₀:ℂ) + (θ:ℂ)*Complex.I).re := by
      rw [Work.Potential.line_re]; exact hs₁
    have hw₂ : ((s₀:ℂ) + (θ:ℂ)*Complex.I).re < Real.log R := by
      rw [Work.Potential.line_re]; exact hs₂
    rw [fderiv_bilinStrip hρ hρR hu hv hw₁ hw₂]
    have hU := Work.Potential.harmonicAt_expLift hρ hρR hu hw₁ hw₂
    have hV := Work.Potential.harmonicAt_expLift hρ hρR hv hw₁ hw₂
    have eU := eq_neg_of_add_eq_zero_left (Work.Potential.dS_dS_add_dI_dI hU)
    have eV := eq_neg_of_add_eq_zero_left (Work.Potential.dS_dS_add_dI_dI hV)
    rw [eU, eV]
    simp only [bilinPrimDeriv]
    ring
  have hzero : (∫ θ in (0:ℝ)..(2*Real.pi),
      fderiv ℝ (bilinStrip u v) ((s₀:ℂ) + (θ:ℂ)*Complex.I) 1) = 0 := by
    have hEq : (fun θ : ℝ => fderiv ℝ (bilinStrip u v) ((s₀:ℂ) + (θ:ℂ)*Complex.I) 1)
        = fun θ : ℝ => - bilinPrimDeriv u v s₀ θ := funext hpoint
    have hFTC : (∫ θ in (0:ℝ)..(2*Real.pi), bilinPrimDeriv u v s₀ θ) = 0 := by
      have hder : ∀ θ ∈ Set.uIcc (0:ℝ) (2*Real.pi),
          HasDerivAt (bilinPrim u v s₀) (bilinPrimDeriv u v s₀ θ) θ :=
        fun θ _ => hasDerivAt_bilinPrim hρ hρR hu hv hs₁ hs₂ θ
      have hcont : Continuous (bilinPrimDeriv u v s₀) := by
        have h1 := (continuous_expLift_line hρ hρR hv hs₁ hs₂).mul
          (continuous_dIdI_line hρ hρR hu hs₁ hs₂)
        have h2 := (continuous_expLift_line hρ hρR hu hs₁ hs₂).mul
          (continuous_dIdI_line hρ hρR hv hs₁ hs₂)
        change Continuous (fun θ : ℝ => Work.Potential.expLift v ((s₀:ℂ) + (θ:ℂ)*Complex.I)
              * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift u)) ((s₀:ℂ) + (θ:ℂ)*Complex.I)
            - Work.Potential.expLift u ((s₀:ℂ) + (θ:ℂ)*Complex.I)
              * Work.Potential.dI (Work.Potential.dI (Work.Potential.expLift v)) ((s₀:ℂ) + (θ:ℂ)*Complex.I))
        exact h1.sub h2
      have hint : IntervalIntegrable (bilinPrimDeriv u v s₀) volume (0:ℝ) (2*Real.pi) :=
        hcont.intervalIntegrable 0 (2*Real.pi)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint,
        bilinPrim_two_pi hρ hρR hu hv hs₁ hs₂, sub_self]
    rw [hEq, intervalIntegral.integral_neg, hFTC, neg_zero]
  rw [hzero] at hd
  exact hd

lemma circleAverage_bilin_eq_re_strip {u v : ℂ → ℝ} {ρ R r : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    (hr : ρ < r) (hrR : r < R) :
    Real.circleAverage (fun z : ℂ => v z * radialDeriv u 0 z - u z * radialDeriv v 0 z) 0 r
      = (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..(2*Real.pi),
          bilinStrip u v ((Real.log r : ℂ) + (θ:ℂ)*Complex.I)).re := by
  have hrpos : 0 < r := lt_trans hρ hr
  have hl₁ : Real.log ρ < Real.log r := Real.log_lt_log hρ hr
  have hl₂ : Real.log r < Real.log R := Real.log_lt_log hrpos hrR
  have hint : IntervalIntegrable
      (fun θ : ℝ => bilinStrip u v ((Real.log r : ℂ) + (θ:ℂ)*Complex.I))
      volume (0:ℝ) (2 * Real.pi) := by
    have hcont : Continuous (fun θ : ℝ => bilinStrip u v ((Real.log r : ℂ) + (θ:ℂ)*Complex.I)) := by
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      have hw₁ : Real.log ρ < ((Real.log r : ℂ) + (θ:ℂ)*Complex.I).re := by
        rw [Work.Potential.line_re]; exact hl₁
      have hw₂ : ((Real.log r : ℂ) + (θ:ℂ)*Complex.I).re < Real.log R := by
        rw [Work.Potential.line_re]; exact hl₂
      exact ContinuousAt.comp' (x := θ) (f := fun θ : ℝ => (Real.log r : ℂ) + (θ:ℂ)*Complex.I)
        (contDiffAt_bilinStrip hρ hρR hu hv hw₁ hw₂).continuousAt (by fun_prop)
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hpt : ∀ θ : ℝ,
      (fun z : ℂ => v z * radialDeriv u 0 z - u z * radialDeriv v 0 z) (circleMap 0 r θ)
        = (bilinStrip u v ((Real.log r : ℂ) + (θ:ℂ)*Complex.I)).re := by
    intro θ
    set W : ℂ := (Real.log r : ℂ) + (θ:ℂ)*Complex.I with hWdef
    have hcirc : circleMap 0 r θ = Complex.exp W := by
      rw [hWdef]
      rw [show circleMap 0 r θ = (r : ℂ) * Complex.exp (θ * Complex.I) by simp [circleMap],
        Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hrpos]
    have hnorm : ‖Complex.exp W‖ = r := by
      rw [hWdef, Complex.norm_exp]
      simp [Real.exp_log hrpos]
    have hW₁ : ρ < ‖Complex.exp W‖ := by rw [hnorm]; exact hr
    have hW₂ : ‖Complex.exp W‖ < R := by rw [hnorm]; exact hrR
    have hUdiff : DifferentiableAt ℝ u (Complex.exp W) := (hu _ hW₁ hW₂).1.differentiableAt (by norm_num)
    have hVdiff : DifferentiableAt ℝ v (Complex.exp W) := (hv _ hW₁ hW₂).1.differentiableAt (by norm_num)
    have hdsu : (Work.Potential.dS (Work.Potential.expLift u) W).re
        = radialDeriv u 0 (Complex.exp W) := Work.Drive.re_fderiv_expLift (V := u) hUdiff
    have hdsv : (Work.Potential.dS (Work.Potential.expLift v) W).re
        = radialDeriv v 0 (Complex.exp W) := Work.Drive.re_fderiv_expLift (V := v) hVdiff
    have hUre : (Work.Potential.expLift u W).re = u (Complex.exp W) := by
      simp [Work.Potential.expLift]
    have hVre : (Work.Potential.expLift v W).re = v (Complex.exp W) := by
      simp [Work.Potential.expLift]
    have hUim : (Work.Potential.expLift u W).im = 0 := by
      simp [Work.Potential.expLift]
    have hVim : (Work.Potential.expLift v W).im = 0 := by
      simp [Work.Potential.expLift]
    rw [hcirc]
    rw [show bilinStrip u v W = Work.Potential.expLift v W * Work.Potential.dS (Work.Potential.expLift u) W
        - Work.Potential.expLift u W * Work.Potential.dS (Work.Potential.expLift v) W from rfl]
    rw [Complex.sub_re, Complex.mul_re, Complex.mul_re, hVim, hVre, hUim, hUre, hdsu, hdsv]
    ring
  rw [Real.circleAverage_def, smul_eq_mul]
  congr 1
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hre := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (a := (0:ℝ))
    (b := 2 * Real.pi) hint
  simp only [Complex.reCLM_apply] at hre
  rw [← hre]

theorem circleAverage_bilin_zero_eq {u v : ℂ → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt v z)
    {r r' : ℝ} (hr : ρ < r) (hrR : r < R) (hr' : ρ < r') (hr'R : r' < R) :
    Real.circleAverage (fun z : ℂ => v z * radialDeriv u 0 z - u z * radialDeriv v 0 z) 0 r =
      Real.circleAverage (fun z : ℂ => v z * radialDeriv u 0 z - u z * radialDeriv v 0 z) 0 r' := by
  have hrpos : 0 < r := lt_trans hρ hr
  have hr'pos : 0 < r' := lt_trans hρ hr'
  have hl₁ : Real.log ρ < Real.log r := Real.log_lt_log hρ hr
  have hl₂ : Real.log r < Real.log R := Real.log_lt_log hrpos hrR
  have hl₁' : Real.log ρ < Real.log r' := Real.log_lt_log hρ hr'
  have hl₂' : Real.log r' < Real.log R := Real.log_lt_log hr'pos hr'R
  have hderiv : ∀ s ∈ Set.Ioo (Real.log ρ) (Real.log R),
      HasDerivAt (fun s : ℝ => ∫ θ in (0:ℝ)..(2*Real.pi),
        bilinStrip u v ((s:ℂ) + (θ:ℂ)*Complex.I)) 0 s :=
    fun s hs => hasDerivAt_bilinStrip_integral hρ hρR hu hv hs.1 hs.2
  have hstrip : (∫ θ in (0:ℝ)..(2*Real.pi), bilinStrip u v ((Real.log r : ℂ) + (θ:ℂ)*Complex.I))
      = (∫ θ in (0:ℝ)..(2*Real.pi), bilinStrip u v ((Real.log r' : ℂ) + (θ:ℂ)*Complex.I)) :=
    IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).deriv) ⟨hl₁, hl₂⟩ ⟨hl₁', hl₂'⟩
  rw [circleAverage_bilin_eq_re_strip hρ hρR hu hv hr hrR,
    circleAverage_bilin_eq_re_strip hρ hρR hu hv hr' hr'R, hstrip]

lemma harmonicAt_comp_add_const {u : ℂ → ℝ} {a : ℂ} {ρ R : ℝ}
    (hu : ∀ z : ℂ, ρ < ‖z - a‖ → ‖z - a‖ < R → InnerProductSpace.HarmonicAt u z) :
    ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ < R → InnerProductSpace.HarmonicAt (fun z : ℂ => u (z + a)) z := by
  intro z hz1 hz2
  have h1 : ρ < ‖z + a - a‖ := by rw [add_sub_cancel_right]; exact hz1
  have h2 : ‖z + a - a‖ < R := by rw [add_sub_cancel_right]; exact hz2
  have hf : AnalyticAt ℂ (fun z : ℂ => z + a) z :=
    analyticAt_id.add (analyticAt_const (v := a))
  have hcomp := Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic hf (hu (z + a) h1 h2)
  simpa [Function.comp] using hcomp

theorem circleFluxBilin_eq_of_harmonicOn_annulus {u v : ℂ → ℝ} {a : ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ∀ z : ℂ, ρ < ‖z - a‖ → ‖z - a‖ < R → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ρ < ‖z - a‖ → ‖z - a‖ < R → InnerProductSpace.HarmonicAt v z)
    {r r' : ℝ} (hr : ρ < r) (hrR : r < R) (hr' : ρ < r') (hr'R : r' < R) :
    Real.circleAverage (fun z : ℂ => v z * Work.Drive.radialDeriv u a z
        - u z * Work.Drive.radialDeriv v a z) a r =
      Real.circleAverage (fun z : ℂ => v z * Work.Drive.radialDeriv u a z
        - u z * Work.Drive.radialDeriv v a z) a r' := by
  set F : ℂ → ℝ := fun w => v w * radialDeriv u a w - u w * radialDeriv v a w with hF
  have hUharm := harmonicAt_comp_add_const (a := a) (ρ := ρ) (R := R) hu
  have hVharm := harmonicAt_comp_add_const (a := a) (ρ := ρ) (R := R) hv
  have hkey := circleAverage_bilin_zero_eq (u := fun z : ℂ => u (z + a)) (v := fun z : ℂ => v (z + a))
    hρ hρR hUharm hVharm hr hrR hr' hr'R
  have hstep : ∀ t : ℝ,
      Real.circleAverage (fun z : ℂ => (fun w : ℂ => v (w + a)) z
          * radialDeriv (fun w : ℂ => u (w + a)) 0 z
        - (fun w : ℂ => u (w + a)) z * radialDeriv (fun w : ℂ => v (w + a)) 0 z) 0 t
      = Real.circleAverage F a t := by
    intro t
    rw [← Real.circleAverage_map_add_const (f := F) (c := a) (R := t)]
    congr 1
    funext z
    rw [hF]
    simp only [radialDeriv_map_add_const]
  rw [hstep r, hstep r'] at hkey
  exact hkey

end Work.Drive
