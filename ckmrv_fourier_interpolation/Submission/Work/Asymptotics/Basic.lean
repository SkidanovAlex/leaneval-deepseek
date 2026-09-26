/-
# The contour integral defining the CKMRV generating functions

This file sets up the objects on which the whole `Work.Asymptotics` chapter rests: the
integrand of the CKMRV transform

  `F₂(τ,r) = 4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`

viewed as a function of the *complex* variable `τ` (so that the parametric-integral theory of
`Mathlib` applies), together with the transfer lemmas identifying it with
`Work.Kernels.kernelTransform`.

## Main definitions

* `Work.Asymptotics.contourKernel K τ t` : `K(τ, it)` for `τ : ℂ` (junk `0` off `ℍ`), the
  integrand's kernel factor; it agrees with `Work.Kernels.Kaxis K τ t` for `τ ∈ ℍ`.
* `Work.Asymptotics.contourIntegrand K r τ t` : `K(τ,it) e^{-πr²t}`.
* `Work.Asymptotics.cotransform K r τ` : `∫_0^∞ K(τ,it) e^{-πr²t} dt`, without the `sin²`
  prefactor (so that it is manifestly a parametric integral).
* `Work.Asymptotics.transformC K r τ` : `4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`, the
  transform appearing in the paper's (5.2).
* `Work.Asymptotics.ContourDom K r U bound` : the assertion that `bound` is an integrable
  dominator for the contour integrand on the open set `U`.
* `Work.Asymptotics.PoleOnContour K τ` : the assertion that some pole of `z ↦ K(τ,z)` lies on
  the positive imaginary axis (the *obstruction* to the naive integral definition of `F₂`;
  see `Work.Asymptotics.Obstruction`).

## Main results

* `Work.Asymptotics.transformC_eq_kernelTransform` : for `τ` in the upper half plane,
  `transformC K r τ = Work.Kernels.kernelTransform K ⟨τ,_⟩ r`.
* `Work.Asymptotics.cotransform_eq_zero_of_not_integrable` : if the contour integrand is not
  integrable then the transform takes the junk value `0` (this is `integral_undef`, and it is
  the mechanism of the obstruction described in `Work.Asymptotics.Obstruction`).
-/
import Mathlib
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

namespace Work.Asymptotics

/-! ## The contour integral -/

/-- The kernel evaluated on the positive imaginary axis, as a function of the *complex*
variable `τ`.  Off the upper half plane it takes the junk value `0`; on the upper half plane
`τ ↦ ofComplex τ` is the identity. -/
def contourKernel (K : ℍ → ℍ → ℂ) (τ : ℂ) (t : ℝ) : ℂ :=
  Work.Kernels.Kaxis K (UpperHalfPlane.ofComplex τ) t

/-- The integrand `K(τ,it) e^{-πr²t}` of the CKMRV contour integral, as a function of
`τ : ℂ`. -/
def contourIntegrand (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℂ) (t : ℝ) : ℂ :=
  contourKernel K τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))

/-- The CKMRV contour integral `∫_0^∞ K(τ,it) e^{-πr²t} dt` without the `sin²` prefactor;
this is the parametric integral whose `τ`-dependence is studied in
`Work.Asymptotics.Holomorphy`. -/
def cotransform (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), contourIntegrand K r τ t

/-- The CKMRV transform `4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt` as a function of `τ : ℂ`. -/
def transformC (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℂ) : ℂ :=
  4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 * cotransform K r τ

/-- The `sin²` prefactor of the CKMRV transform. -/
def sinSq (r : ℝ) : ℂ := 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2

@[simp] lemma transformC_eq (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℂ) :
    transformC K r τ = sinSq r * cotransform K r τ := rfl

/-- On the upper half plane the complex parametrisation agrees with the kernel restricted to
`ℍ`. -/
lemma contourKernel_eq_Kaxis (K : ℍ → ℍ → ℂ) {τ : ℂ} (hτ : 0 < τ.im) (t : ℝ) :
    contourKernel K τ t = Work.Kernels.Kaxis K ⟨τ, hτ⟩ t := by
  rw [contourKernel, UpperHalfPlane.ofComplex_apply_of_im_pos hτ]

/-- **The transform on `ℂ` restricts to the paper's transform on `ℍ`.** -/
theorem transformC_eq_kernelTransform (K : ℍ → ℍ → ℂ) (r : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    transformC K r τ = Work.Kernels.kernelTransform K ⟨τ, hτ⟩ r := by
  have h : cotransform K r τ
      = ∫ t in Set.Ioi (0 : ℝ),
          Work.Kernels.Kaxis K ⟨τ, hτ⟩ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    rw [cotransform]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [contourIntegrand, contourKernel_eq_Kaxis K hτ t]
  show 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 * _ = _
  rw [h]
  rfl

/-! ## Dominators on the contour -/

/-- `ContourDom K r U bound` : `bound` is an integrable dominator for the contour integrand
`t ↦ K(τ,it)e^{-πr²t}` on the open set `U ⊆ ℂ` of the `τ`-variable.  This is the exact
hypothesis needed for the parametric-integral theorems, and it is the analytic input that the
concrete estimates of `Work.Asymptotics.Cleared` provide. -/
def ContourDom (K : ℍ → ℍ → ℂ) (r : ℝ) (U : Set ℂ) (bound : ℝ → ℝ) : Prop :=
  IntegrableOn bound (Set.Ioi (0 : ℝ)) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ τ ∈ U, ‖contourIntegrand K r τ t‖ ≤ bound t

/-- The integrand is dominated on a *neighbourhood* of `τ₀`. -/
def LocContourDom (K : ℍ → ℍ → ℂ) (r : ℝ) (τ₀ : ℂ) : Prop :=
  ∃ U ∈ 𝓝 τ₀, ∃ bound : ℝ → ℝ, ContourDom K r U bound

/-- `PoleOnContour K τ` : some pole of `z ↦ K(τ,z)` lies on the positive imaginary axis, i.e.
`K` has a singularity at some point `it`, `t > 0` (as a function of its second variable).  This
is the precise obstruction to reading the transform `F₂` off the naive integral: when it holds
the integrand `t ↦ K(τ,it)e^{-πr²t}` fails to be integrable, so `Mathlib`'s integral — and
hence `Work.Kernels.kernelTransform` — takes the junk value `0` there.  See
`Work.Asymptotics.Obstruction`. -/
def PoleOnContour (K : ℍ → ℍ → ℂ) (τ : ℍ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ¬ DifferentiableAt ℂ (fun z : ℂ => K τ (UpperHalfPlane.ofComplex z))
      ((t : ℂ) * Complex.I)

/-- `ContourClean K τ` : no pole of `z ↦ K(τ,z)` on the positive imaginary axis; equivalently
`z ↦ K(τ,z)` is holomorphic on a neighbourhood of the contour (this is the hypothesis under
which the CKMRV integral converges and represents the paper's `F₂`). -/
def ContourClean (K : ℍ → ℍ → ℂ) (τ : ℍ) : Prop := ¬ PoleOnContour K τ

/-! ## The junk value of the integral -/

/-- If the contour integrand is not integrable then the transform is `0`, because `Mathlib`'s
Bochner integral assigns the value `0` to every non-integrable function.  This is the
mechanism by which the naive integral definition of `F₂` degenerates at a point where the
contour carries a pole. -/
theorem cotransform_eq_zero_of_not_integrable (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℂ)
    (h : ¬ IntegrableOn (contourIntegrand K r τ) (Set.Ioi (0 : ℝ))) : cotransform K r τ = 0 := by
  show (∫ t, contourIntegrand K r τ t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 0
  exact integral_undef h

end Work.Asymptotics
