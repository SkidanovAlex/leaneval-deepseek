/-
# The obstruction: the naive contour integral is *not* the paper's `F₂`

This file records the exact point at which the naive reading of CKMRV (5.2) breaks, so that the
rest of the chapter (and the caller) is not built on a false statement.

## The mathematics

CKMRV define the generating function by the formal expression

  `F(τ,r) = e^{πiτr²} + 4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`   (5.2)

but they immediately observe that "we have not yet addressed when the integral is defined": the
integral is convergent *only* for `τ` in the fundamental domain `𝒟` of `Γ(2)` (where no pole of
`z ↦ K(τ,z)` lies on the contour), and the function `F` of Theorem 3.1 is obtained from that
piece by *analytic continuation* (their Proposition 4.6, "the continuation of `F` from `𝒟` to
`ℍ`"), using the functional equations and the residue computations.

The kernels have a simple pole at every `z ∈ SL(2,ℤ)τ`, with residue proportional to
`φ(γ)`, where `φ(I) = φ(S) = 0` but `φ(T) = 1` (Theorem 4.9(3)).  Consequently, for every
`τ = 1 + it` (`t > 0`) the pole at `z = T^{-1}τ = it` lies **on** the integration contour, and
more generally this happens for the whole `SL(2,ℤ)`-orbit of the imaginary axis.  At such a
point the integrand `t ↦ K(τ,it)e^{-πr²t}` has a non-removable `1/(t-t₀)` singularity, hence is
not integrable, and `Mathlib`'s Bochner integral assigns it the junk value `0`; and as `σ → τ`
through the complementary (dense) set the integral blows up logarithmically.

So the function `τ ↦ Work.Kernels.kernelTransform K τ r`, read literally as "the integral", is
**not** holomorphic on `ℍ`, and `Work.Kernels.SatisfiesThm31 d k₀ (Fgen K) (Ftgen K̂)` cannot be
proved from it.  The corrected statement — the one this chapter reduces to the kernel estimates
— is holomorphy on a *contour-clean* open set (see `Work.Asymptotics.Holomorphy` and
`Work.Asymptotics.ContourClean`), together with the propagation of the functional equations from
that set to `ℍ` (CKMRV Proposition 3.2).

## What is proved here

* `Work.Asymptotics.HasContourPole` : the exact hypothesis "the contour integrand has a
  non-removable simple pole at `t₀ > 0`", i.e. the output of the residue computation of Theorem
  4.9(3) (`φ(T) = 1`).
* `Work.Asymptotics.not_integrableOn_contourIntegrand_of_hasContourPole` : such a pole makes the
  integrand non-integrable.
* `Work.Asymptotics.kernelTransform_eq_zero_of_hasContourPole` and
  `Work.Asymptotics.Fgen_eq_gaussTerm_of_hasContourPole` : the transform then takes the junk
  value `0`, so that `Fgen K τ r` collapses to `gaussTerm τ r`.

## What is *not* proved here (the remaining input)

That the pole of `z ↦ K(τ,z)` at `z = T^{-1}τ` is genuinely present with non-vanishing residue
requires the residue computation of CKMRV Theorem 4.9(3) for the explicit kernels of
`Work.Kernels`: `Res_{τ=γz} K_± = -(j(γ,z)^{d/2-2}/2π) φ_±(γ)` with `φ_±(T) = 1 ≠ 0`, proved in
the paper by the explicit computation of
`Res_{τ=z}Υ^{(d)}_±`.  In this workspace the cleared kernels "have no poles" by construction, so
establishing the non-vanishing residue is exactly the missing lemma
(`Work.Asymptotics.Kfun_residue_at_T`): it is a finite algebraic computation with
`j'(z) = -2πiE₄(z)²E₆(z)/Δ(z)`, `E₆E₈ = E₄E₁₀ = E₁₄`, `E₂|₂S = E₂ - 6i/(πz)` and the
non-vanishing of `E₄`, `E₆` at the chosen contour point.
-/
import Mathlib
import Submission.Work.Asymptotics.Basic
import Submission.Work.Asymptotics.not_integrableOn_of_simplePole

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics

/-- **A non-removable simple pole of the contour integrand.**  `HasContourPole K r τ` says that
the integrand `t ↦ K(τ,it)e^{-πr²t}` has a pole `c/(t-t₀)` with non-vanishing residue at some
`t₀ > 0`, modulo a locally bounded function.  This is the shape in which CKMRV Theorem 4.9(3)
(`Res_{τ=z}(K|^τ_{d/2}r) = -φ(r)/2π` with `φ(T) = 1`) delivers the obstruction. -/
def HasContourPole (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : Prop :=
  ∃ (t₀ : ℝ) (c : ℂ) (g : ℝ → ℂ), 0 < t₀ ∧ c ≠ 0 ∧
    (∃ M : ℝ, ∀ᶠ t in 𝓝 t₀, ‖g t‖ ≤ M) ∧
    ∀ᶠ t in 𝓝 t₀, (Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = c / ((t : ℂ) - t₀) + g t

/-- A contour pole makes the integrand non-integrable on `(0,∞)`. -/
theorem not_integrableOn_contourIntegrand_of_hasContourPole {K : ℍ → ℍ → ℂ} {r : ℝ} {τ : ℍ}
    (h : HasContourPole K r τ) :
    ¬ IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨t₀, c, g, ht₀, hc, hg, hf⟩ := h
  exact not_integrableOn_of_simplePole ht₀ hc hg hf

/-- **The junk value.**  At a point where the contour integrand has a non-removable pole, the
CKMRV transform takes the junk value `0`. -/
theorem kernelTransform_eq_zero_of_hasContourPole {K : ℍ → ℍ → ℂ} {r : ℝ} {τ : ℍ}
    (h : HasContourPole K r τ) : Work.Kernels.kernelTransform K τ r = 0 := by
  have hni := not_integrableOn_contourIntegrand_of_hasContourPole h
  have hzero : (∫ t in Set.Ioi (0 : ℝ),
      Work.Kernels.Kaxis K τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = 0 := by
    show (∫ t, (Work.Kernels.Kaxis K τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 0
    exact integral_undef hni
  simp only [Work.Kernels.kernelTransform, hzero, mul_zero]

/-- Consequently the generating function collapses to the Gaussian term at such a point. -/
theorem Fgen_eq_gaussTerm_of_hasContourPole {K : ℍ → ℍ → ℂ} {r : ℝ} {τ : ℍ}
    (h : HasContourPole K r τ) : Work.Kernels.Fgen K τ r = Work.Kernels.gaussTerm τ r := by
  simp only [Work.Kernels.Fgen, kernelTransform_eq_zero_of_hasContourPole h, add_zero]

/-- The same for `F̃ = Ftgen K̂`. -/
theorem Ftgen_eq_zero_of_hasContourPole {K : ℍ → ℍ → ℂ} {r : ℝ} {τ : ℍ}
    (h : HasContourPole K r τ) : Work.Kernels.Ftgen K τ r = 0 := by
  simp only [Work.Kernels.Ftgen, kernelTransform_eq_zero_of_hasContourPole h]

end Work.Asymptotics
