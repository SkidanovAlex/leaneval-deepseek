import Mathlib

/-! # A continuous `n`-th root of a holomorphic function is holomorphic.

Auxiliary lemma for `Work.Smooth.SphereJordan.planeDomain_homeo_unitBall`
(the "square root trick" in the proof of the Riemann mapping theorem).

If `h : ℂ → ℂ` is continuous on an open set `U`, `h z ≠ 0` on `U`, `h z ^ n = F z` on `U`
with `F` holomorphic on `U` and `n > 0`, then `h` is holomorphic on `U`.

The proof is local: near a point `z₀ ∈ U`, the function `w ↦ w ^ n` is a local biholomorphism at
`h z₀` (its derivative `n * (h z₀) ^ (n-1)` is nonzero), and `h` agrees with the local inverse of
`w ↦ w ^ n` composed with `F`.
-/

namespace Work.Smooth.SphereJordan

open Filter
open scoped Topology

theorem differentiableOn_of_pow_eq {U : Set ℂ} (hU : IsOpen U) {F h : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (hF : DifferentiableOn ℂ F U) (hh : ContinuousOn h U) (hne : ∀ z ∈ U, h z ≠ 0)
    (heq : ∀ z ∈ U, h z ^ n = F z) : DifferentiableOn ℂ h U := by
  intro z₀ hz₀
  have hw₀ : h z₀ ≠ 0 := hne z₀ hz₀
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQ : HasStrictDerivAt (fun w : ℂ => w ^ n) ((n : ℂ) * h z₀ ^ (n - 1)) (h z₀) :=
    hasStrictDerivAt_pow n (h z₀)
  have hQ' : ((n : ℂ) * h z₀ ^ (n - 1)) ≠ 0 :=
    mul_ne_zero hn' (pow_ne_zero _ hw₀)
  set Ψ : ℂ → ℂ := HasStrictDerivAt.localInverse (f := fun w : ℂ => w ^ n)
    (f' := (n : ℂ) * h z₀ ^ (n - 1)) (a := h z₀) hQ hQ' with hΨ
  have hleft : ∀ᶠ w in 𝓝 (h z₀), Ψ (w ^ n) = w := by
    simpa [hΨ] using HasStrictDerivAt.eventually_left_inverse (f := fun w : ℂ => w ^ n)
      (f' := (n : ℂ) * h z₀ ^ (n - 1)) (a := h z₀) hQ hQ'
  have hderiv : HasStrictDerivAt Ψ (((n : ℂ) * h z₀ ^ (n - 1))⁻¹) (h z₀ ^ n) := by
    simpa [hΨ] using HasStrictDerivAt.to_localInverse (f := fun w : ℂ => w ^ n)
      (f' := (n : ℂ) * h z₀ ^ (n - 1)) (a := h z₀) hQ hQ'
  have hFz : F z₀ = h z₀ ^ n := (heq z₀ hz₀).symm
  have hcont : Tendsto h (𝓝 z₀) (𝓝 (h z₀)) := hh.continuousAt (hU.mem_nhds hz₀)
  have hev : h =ᶠ[𝓝 z₀] fun z => Ψ (F z) := by
    filter_upwards [hU.mem_nhds hz₀, hcont.eventually hleft] with z hzU hz1
    rw [heq z hzU] at hz1
    exact hz1.symm
  have hcomp : DifferentiableAt ℂ (fun z => Ψ (F z)) z₀ := by
    have h1 : DifferentiableAt ℂ Ψ (F z₀) := by
      rw [hFz]
      exact hderiv.hasDerivAt.differentiableAt
    exact h1.comp z₀ (hF.differentiableAt (hU.mem_nhds hz₀))
  exact (hcomp.congr_of_eventuallyEq hev).differentiableWithinAt

end Work.Smooth.SphereJordan
