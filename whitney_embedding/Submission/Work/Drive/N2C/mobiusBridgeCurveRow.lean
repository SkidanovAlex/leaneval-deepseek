import Mathlib
import Submission.Work.Drive.N2Lead.mobius_bridgeStar
import Submission.Work.Drive.N2Lead.twistToolkit

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-!
# The twisted, pushed polar-bridge curve: the two pointwise rows

This file proves `Work.Drive.N2C.mobiusBridgeCurveRow`, the bridge-zone curve row about the origin
of the Möbius certificate.  The curve is

`P φ = proj2 (pushY Dp εp 1 (twistX ε (-1) (cE3 (r φ · e^{iφ}))))`,

where `cE3 (x + iy) = (x, y, 0)` and

* `twistX ε (-1) v = rot12 (-π · τ((v₀ + ε)/(2ε))) v` — the vertical slab twist at the angle `-1`;
* `pushY Dp εp 1` — the vertical push with the one-dimensional profile `pushProf Dp εp 1`.

The hypothesis `hεsmall` puts the curve on the near side `x ≥ ε` of the slab of `twistX`, where the
twist is the **half-turn** `rot12 (-π)`:  `twistX ε (-1) v = (v₀, -v₁, -v₂)`
(`Work.Drive.N2Lead.twistX_neg_one_of_le`).  Consequently, on the whole interval,

`P φ = X φ + i · ψ (-Y φ)` with `X φ = r φ cos φ`, `Y φ = r φ sin φ`, `ψ = pushProf Dp εp 1`,

and since `x ≥ ε > 0` the projection never vanishes, while the angular rate
`x y' - y x'` of `P` is `-bridgeRate r Dp εp φ`, which is *strictly positive* on `[-φE, φE]` by
`Work.Drive.N2Lead.mobius_bridgeStar` (the exported steps `bridgeRate_pos` / `bridgeRate_even`).

The two rows the certificate consumes are

* `proj2 P φ ≠ 0` — from `Re P φ = X φ ≥ ε > 0`;
* `(star (proj2 P φ) · deriv (proj2 P) φ).im ≠ 0` — because the imaginary part of
  `(a - ib)(a' + ib')` is `a b' - b a' = x y' - y x'`, the angular rate.

The formal core is the *explicit* model function
`brM r Dp εp ε ψ = (X ψ : ℂ) + (ψ (brB r ε ψ) : ℂ) · I`, where `brB r ε ψ = Y ψ · cos (brT r ε ψ)`
and `brT r ε ψ = π · τ((X ψ + ε)/(2ε))` are the two components of the twisted point.  The curve
`P` agrees with `brM` **as a function of `φ`** (`pushTwist_proj2_eq`), which is what lets the chain
rule be applied at the endpoints of `[-φE, φE]`; there the angle is pinned to `π`, so
`cos (brT r ε φ) = -1` and `sin (brT r ε φ) = 0`, the latter killing the (unknown) derivative of the
angle and leaving exactly the rate of the untwisted pushed curve.
-/

/-- The `x`-coordinate `r φ · cos φ` of the polar bridge curve. -/
def brX (r : ℝ → ℝ) (ψ : ℝ) : ℝ := r ψ * Real.cos ψ

/-- The `y`-coordinate `r φ · sin φ` of the polar bridge curve. -/
def brY (r : ℝ → ℝ) (ψ : ℝ) : ℝ := r ψ * Real.sin ψ

/-- The twist angle `π · τ((X ψ + ε)/(2ε))` of `twistX ε (-1)` at the polar point. -/
def brT (r : ℝ → ℝ) (ε ψ : ℝ) : ℝ := Real.pi * Real.smoothTransition ((brX r ψ + ε) / (2 * ε))

/-- The `y`-coordinate of the twisted polar point. -/
def brB (r : ℝ → ℝ) (ε ψ : ℝ) : ℝ := brY r ψ * Real.cos (brT r ε ψ)

/-- The vertical coordinate of the pushed, twisted polar point. -/
def brP (r : ℝ → ℝ) (Dp εp ε ψ : ℝ) : ℝ := Work.Drive.N2Lead.pushProf Dp εp 1 (brB r ε ψ)

/-- The planar projection of the pushed, twisted polar point, as a complex number: the model
function of the bridge-zone curve row. -/
def brM (r : ℝ → ℝ) (Dp εp ε : ℝ) (ψ : ℝ) : ℂ :=
  ((brX r ψ : ℝ) : ℂ) + ((brP r Dp εp ε ψ : ℝ) : ℂ) * Complex.I

/-! ### The value of the curve -/

/-- The second coordinate of `rot12 t v`. -/
theorem rot12_apply_one (t : ℝ) (v : Work.Drive.N2Lead.E3) :
    (Work.Drive.N2Lead.rot12 t v) 1 = v 1 * Real.cos t - v 2 * Real.sin t := by
  simp [Work.Drive.N2Lead.rot12]

/-- The second coordinate of the vertical slab twist at the angle `-1`. -/
theorem twistX_apply_one (ε : ℝ) (v : Work.Drive.N2Lead.E3) :
    (Work.Drive.N2Lead.twistX ε (-1) v) 1 = v 1 * Real.cos (Work.Drive.N2Lead.twistAngleX ε v)
      + v 2 * Real.sin (Work.Drive.N2Lead.twistAngleX ε v) := by
  rw [Work.Drive.N2Lead.twistX_eq, rot12_apply_one]
  rw [show (-1 : ℝ) * Work.Drive.N2Lead.twistAngleX ε v = -Work.Drive.N2Lead.twistAngleX ε v
      from by ring, Real.cos_neg, Real.sin_neg]
  ring

/-- **The explicit value of the bridge-zone curve.**  For *every* parameter `ψ` the planar
projection of the pushed, twisted polar point is the complex number `brM r Dp εp ε ψ`; the third
coordinate of the polar point is `0`, so the twist only rotates the `y`-coordinate by the angle
`brT r ε ψ`. -/
theorem pushTwist_proj2_eq (r : ℝ → ℝ) (Dp εp ε ψ : ℝ) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (r ψ * Complex.exp ((ψ : ℂ) * Complex.I))))) = brM r Dp εp ε ψ := by
  have hc0 := Work.Drive.N2Lead.bridgePt_zero r ψ
  have hc1 := Work.Drive.N2Lead.bridgePt_one r ψ
  have hc2 := Work.Drive.N2Lead.bridgePt_two r ψ
  have ht1 : (Work.Drive.N2Lead.twistX ε (-1)
      (Work.Drive.N2.cE3 (r ψ * Complex.exp ((ψ : ℂ) * Complex.I)))) 1
      = brY r ψ * Real.cos (brT r ε ψ) := by
    rw [twistX_apply_one, Work.Drive.N2Lead.twistAngleX, hc0, hc1, hc2]
    simp only [brY, brT, brX, zero_mul, add_zero]
  have ht0 : (Work.Drive.N2Lead.twistX ε (-1)
      (Work.Drive.N2.cE3 (r ψ * Complex.exp ((ψ : ℂ) * Complex.I)))) 0 = brX r ψ := by
    rw [Work.Drive.N2Lead.twistX_first, hc0, brX]
  apply Complex.ext
  · simp only [Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.pushY_apply_zero, ht0, brM, brX,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero]
    ring
  · simp only [Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.pushY_apply_one, ht1, brM, brP, brB,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, add_zero, mul_one]
    ring

/-! ### The derivative of the model function -/

/-- The imaginary part of `(star z) · w` for `z = a + b i` and `w = c + d i`, in coordinates. -/
theorem star_mul_I_im (a b c d : ℝ) :
    (star (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I)
      * (((c : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I)).im = a * d - b * c := by
  rw [Complex.mul_im]
  simp
  ring

/-- A complex-valued function is differentiable with derivative `a + b i` as soon as its real and
imaginary parts have the derivatives `a` and `b` (`ℝ`-linearity of `ℂ`). -/
theorem hasDerivAt_complex_of_re_im {g : ℝ → ℂ} {x a b : ℝ}
    (ha : HasDerivAt (fun y => (g y).re) a x) (hb : HasDerivAt (fun y => (g y).im) b x) :
    HasDerivAt g ((a : ℂ) + (b : ℂ) * Complex.I) x := by
  have key : ∀ (f : ℝ → ℝ) (c : ℝ), HasDerivAt f c x →
      HasDerivAt (fun y : ℝ => ((f y : ℝ) : ℂ)) ((c : ℝ) : ℂ) x := by
    intro f c hf
    have h := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
    have hd := h.hasDerivAt
    have hderiv : ((Complex.ofRealCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ c) 1)
        = ((c : ℝ) : ℂ) := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    have hd' := hd.congr_deriv hderiv
    exact hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => rfl))
  have h1 := key (fun y => (g y).re) a ha
  have h2 := key (fun y => (g y).im) b hb
  have hsum := h1.add (h2.mul_const Complex.I)
  have hfun : g = fun y : ℝ => ((g y).re : ℂ) + ((g y).im : ℂ) * Complex.I :=
    funext fun y => (Complex.re_add_im (g y)).symm
  rw [hfun]
  exact hsum

theorem hasDerivAt_brX (r : ℝ → ℝ) (φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (brX r) (deriv r φ * Real.cos φ - r φ * Real.sin φ) φ := by
  have h : HasDerivAt (fun u : ℝ => brX r u) (deriv r φ * Real.cos φ - r φ * Real.sin φ) φ := by
    simpa only [brX] using Work.Drive.N2Lead.hasDerivAt_mul_cos hr
  exact h

theorem hasDerivAt_brY (r : ℝ → ℝ) (φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (brY r) (deriv r φ * Real.sin φ + r φ * Real.cos φ) φ := by
  have h : HasDerivAt (fun u : ℝ => brY r u) (deriv r φ * Real.sin φ + r φ * Real.cos φ) φ := by
    simpa only [brY] using Work.Drive.N2Lead.hasDerivAt_mul_sin hr
  exact h

theorem differentiableAt_brT (r : ℝ → ℝ) (ε φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    DifferentiableAt ℝ (brT r ε) φ := by
  have hX : DifferentiableAt ℝ (brX r) φ := (hasDerivAt_brX r φ hr).differentiableAt
  have hj : DifferentiableAt ℝ (fun ψ : ℝ => (brX r ψ + ε) / (2 * ε)) φ :=
    (hX.add_const ε).div_const (2 * ε)
  have hτ : DifferentiableAt ℝ (fun t : ℝ => Real.smoothTransition t)
      ((brX r φ + ε) / (2 * ε)) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt
  have hcomp := hτ.comp φ hj
  have h : DifferentiableAt ℝ
      (fun ψ : ℝ => Real.pi * Real.smoothTransition ((brX r ψ + ε) / (2 * ε))) φ :=
    (differentiableAt_const (Real.pi)).mul hcomp
  exact DifferentiableAt.congr_of_eventuallyEq h
    (Filter.Eventually.of_forall (fun u => by simp only [brT]))

theorem hasDerivAt_brT (r : ℝ → ℝ) (ε φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (brT r ε) (deriv (brT r ε) φ) φ := (differentiableAt_brT r ε φ hr).hasDerivAt

theorem hasDerivAt_brB (r : ℝ → ℝ) (ε φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (brB r ε) ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
      + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ)) φ := by
  have hY := hasDerivAt_brY r φ hr
  have hc : HasDerivAt (fun u : ℝ => Real.cos (brT r ε u))
      (-Real.sin (brT r ε φ) * deriv (brT r ε) φ) φ := (hasDerivAt_brT r ε φ hr).cos
  have h := hY.mul hc
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => ?_))
  simp only [brB, Pi.mul_apply]

theorem hasDerivAt_brP (r : ℝ → ℝ) (Dp εp ε φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (brP r Dp εp ε)
      (deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brB r ε φ)
        * ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
          + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ))) φ := by
  have hB := hasDerivAt_brB r ε φ hr
  have h := (Work.Drive.N2Lead.differentiable_pushProf Dp εp 1 (brB r ε φ)).hasDerivAt.comp φ hB
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => ?_))
  simp only [brP, Function.comp_apply]

theorem hasDerivAt_brM (r : ℝ → ℝ) (Dp εp ε φ : ℝ) (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (brM r Dp εp ε)
      (((deriv r φ * Real.cos φ - r φ * Real.sin φ : ℝ) : ℂ)
        + ((deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brB r ε φ)
            * ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
              + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ)) : ℝ) : ℂ)
          * Complex.I) φ := by
  have hX := hasDerivAt_brX r φ hr
  have hP := hasDerivAt_brP r Dp εp ε φ hr
  have hre : HasDerivAt (fun y : ℝ => (brM r Dp εp ε y).re)
      (deriv r φ * Real.cos φ - r φ * Real.sin φ) φ :=
    hX.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by simp [brM]))
  have him : HasDerivAt (fun y : ℝ => (brM r Dp εp ε y).im)
      (deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brB r ε φ)
        * ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
          + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ))) φ :=
    hP.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by simp [brM]))
  exact hasDerivAt_complex_of_re_im hre him

/-! ### The angular rate of the curve is `-bridgeRate` -/

/-- **The rate of the bridge-zone curve.**  If the polar `x`-coordinate `brX r φ = r φ cos φ` is at
least `ε`, the twist at `φ` is the half-turn `rot12 (-π)`, so

`(star (proj2 P φ) · deriv (proj2 P) φ).im = -bridgeRate r Dp εp φ`.

Indeed the imaginary part is the angular rate `x y' - y x'`; the twist negates the height, hence the
rate is that of the pushed polar curve with the *opposite* sign, i.e. `-bridgeRate`.  The (unknown)
derivative of the twist angle disappears because `sin (brT r ε φ) = sin π = 0`, and the values
`cos (brT r ε φ) = -1`, `brB r ε φ = -brY r φ` together with the oddness of `pushProf` (and the
evenness of its derivative, `Work.Drive.N2Lead.deriv_odd_eq`) turn the model rate into `-bridgeRate`. -/
theorem brM_rate (r : ℝ → ℝ) (Dp εp ε φ : ℝ) (hr : DifferentiableAt ℝ r φ)
    (hε : 0 < ε) (hεp : 0 < εp) (hbig : ε ≤ brX r φ) :
    (star (brM r Dp εp ε φ) * deriv (brM r Dp εp ε) φ).im
      = - Work.Drive.N2Lead.bridgeRate r Dp εp φ := by
  have hderiv := (hasDerivAt_brM r Dp εp ε φ hr).deriv
  have hj : (1 : ℝ) ≤ (brX r φ + ε) / (2 * ε) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hτ1 : Real.smoothTransition ((brX r φ + ε) / (2 * ε)) = 1 :=
    Real.smoothTransition.one_of_one_le hj
  have hT : brT r ε φ = Real.pi := by simp only [brT, hτ1, mul_one]
  have hcos : Real.cos (brT r ε φ) = -1 := by rw [hT, Real.cos_pi]
  have hsin : Real.sin (brT r ε φ) = 0 := by rw [hT, Real.sin_pi]
  have hBval : brB r ε φ = -brY r φ := by simp only [brB, hcos]; ring
  have hPval : brP r Dp εp ε φ = -Work.Drive.N2Lead.pushProf Dp εp 1 (brY r φ) := by
    rw [brP, hBval,
      Work.Drive.N2Lead.pushProf_odd (D := Dp) (εp := εp) (s := 1) (ne_of_gt hεp)]
  have hodd : deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (-(brY r φ))
      = deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brY r φ) :=
    Work.Drive.N2Lead.deriv_odd_eq (B := Work.Drive.N2Lead.pushProf Dp εp 1)
      (fun y => Work.Drive.N2Lead.pushProf_odd (D := Dp) (εp := εp) (s := 1) (ne_of_gt hεp)
        (y := y))
      (fun y => Work.Drive.N2Lead.differentiable_pushProf Dp εp 1 y) (brY r φ)
  have hkey : (star (brM r Dp εp ε φ) * deriv (brM r Dp εp ε) φ).im
      = brX r φ * (deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brB r ε φ)
          * ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
            + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ)))
        - brP r Dp εp ε φ * (deriv r φ * Real.cos φ - r φ * Real.sin φ) := by
    rw [hderiv]
    have h := star_mul_I_im (brX r φ) (brP r Dp εp ε φ)
      (deriv r φ * Real.cos φ - r φ * Real.sin φ)
      (deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brB r ε φ)
        * ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
          + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ)))
    simpa only [brM] using h
  rw [hkey]
  have hP' : deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brB r ε φ)
      * ((deriv r φ * Real.sin φ + r φ * Real.cos φ) * Real.cos (brT r ε φ)
        + brY r φ * (-Real.sin (brT r ε φ) * deriv (brT r ε) φ))
      = -(deriv (Work.Drive.N2Lead.pushProf Dp εp 1) (brY r φ)
          * (deriv r φ * Real.sin φ + r φ * Real.cos φ)) := by
    rw [hcos, hsin, hBval, hodd]
    ring
  rw [hP', hPval, Work.Drive.N2Lead.bridgeRate, Work.Drive.N2Lead.bridgeCurve_zero,
    Work.Drive.N2Lead.bridgeCurve_one, Work.Drive.N2Lead.deriv_bridgeCurve_zero hr,
    Work.Drive.N2Lead.deriv_bridgeCurve_one hr, brX, brY]
  ring

/-! ### The bridge-zone curve row -/

/-- **The two pointwise rows of the twisted, pushed polar bridge.**  Let `r` be the radial profile
of `Work.Drive.N2Lead.mobius_lowerProfile` — smooth, positive, even, nonincreasing on `[0, φE]`,
with `ηs² + m² ≤ r²` on `[0, φE]` — and let `φE = mobiusPhiE ηs m`.  Assume the slab half-width `ε`
is small enough that `ε ≤ r φ cos φ` on `[-φE, φE]` (`hεsmall`, the polar curve stays on the near
side of the vertical slab).  Then for every `φ ∈ [-φE, φE]` the planar projection of the pushed,
twisted polar point is non-zero and its angular rate about the origin, i.e. the imaginary part of
`(star z) · z'`, is non-zero: the polar bridge, twisted and pushed, is star-shaped about the origin
on the whole bridge zone. -/
theorem mobiusBridgeCurveRow {ηs m φE ε εp Dp : ℝ} {r : ℝ → ℝ} (hηs : 0 < ηs)
    (hφE : φE = Work.Drive.N2Lead.mobiusPhiE ηs m) (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    (hrsm : ContDiff ℝ 1 r) (hrpos : ∀ φ : ℝ, 0 < r φ) (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) φE, Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hrdec : ∀ φ ∈ Set.Icc (0 : ℝ) φE, deriv r φ ≤ 0)
    (hεsmall : ∀ φ ∈ Set.Icc (-φE) φE, ε ≤ r φ * Real.cos φ) :
    ∀ φ ∈ Set.Icc (-φE) φE,
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))))) ≠ 0 ∧
      (star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))))))
        * deriv (fun ψ : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 (r ψ * Complex.exp ((ψ : ℂ) * Complex.I))))))
          φ).im ≠ 0 := by
  intro φ hφ
  have hr : DifferentiableAt ℝ r φ := (hrsm.differentiable (by simp)).differentiableAt
  have hrall : ∀ ψ : ℝ, DifferentiableAt ℝ r ψ :=
    fun ψ => (hrsm.differentiable (by simp)).differentiableAt
  have hXbig : ε ≤ brX r φ := by
    have h := hεsmall φ hφ
    simpa only [brX] using h
  have hφE' : φE ≤ Real.pi / 2 := by
    rw [hφE]; exact (Work.Drive.N2Lead.mobiusPhiE_mem_Icc ηs m).2
  -- the angular rate of the pushed polar curve is strictly positive on `[-φE, φE]`
  have hpos : 0 < Work.Drive.N2Lead.bridgeRate r Dp εp φ := by
    rcases lt_or_ge (0 : ℝ) φ with h | h
    · exact Work.Drive.N2Lead.bridgeRate_pos hrpos hrdec hrall hDp hεp hφE' ⟨h.le, hφ.2⟩
    · have h1 : 0 ≤ -φ := neg_nonneg.mpr h
      have h2 : -φ ≤ φE := by linarith [hφ.1]
      have hp := Work.Drive.N2Lead.bridgeRate_pos hrpos hrdec hrall hDp hεp hφE' ⟨h1, h2⟩
      rwa [Work.Drive.N2Lead.bridgeRate_even hrev (ne_of_gt hεp) hrall φ] at hp
  constructor
  · -- the projection is non-zero because its real part is `brX r φ ≥ ε > 0`
    rw [pushTwist_proj2_eq r Dp εp ε φ]
    intro hzero
    have hre : (brM r Dp εp ε φ).re = brX r φ := by simp [brM]
    have : brX r φ = 0 := by rw [← hre, hzero]; simp
    linarith
  · -- the angular rate is `-bridgeRate < 0`
    rw [pushTwist_proj2_eq r Dp εp ε φ]
    have hfun : (fun ψ : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2.cE3 (r ψ * Complex.exp ((ψ : ℂ) * Complex.I))))))
        = brM r Dp εp ε := funext (fun ψ => pushTwist_proj2_eq r Dp εp ε ψ)
    rw [hfun, brM_rate r Dp εp ε φ hr hε hεp hXbig]
    intro hz
    linarith

end

end Work.Drive.N2C
