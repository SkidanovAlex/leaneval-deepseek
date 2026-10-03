import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea5.S16.holoGaussian2d

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators

/-- **Geometric core of `allZPerXi`** (the Hecke character factor `χ₀` is absent).

For `0 < q` and `0 < u`, the `m`-fold binomial sum of the one-dimensional Fourier
transforms of `x ↦ x ^ k * exp (-π u x²)`, evaluated at the dual frequency
`(ξ₁/q, ξ₂/q)`, collapses to the `m`-th power of the holomorphic Gaussian phase
`(ξ₁ + iξ₂)/q`:
  `∑_l C(m,l) i^l 𝓕(x^{m-l} e^{-πux²})(ξ₁/q) 𝓕(y^l e^{-πuy²})(ξ₂/q)
      = (-i)^m u^{-(m+1)} ((ξ₁+iξ₂)/q)^m exp(-π(ξ₁²+ξ₂²)/(u q²))`. -/
theorem allZPerXi_core (q : ℕ) (hq : 0 < q) (m : ℕ) {u : ℝ} (hu : 0 < u) (ξ : ℤ × ℤ) :
    (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / (q : ℝ))
          * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / (q : ℝ))))
      = (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
          ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (q : ℂ)) ^ m *
            Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
              / ((u : ℂ) * (q : ℂ) ^ 2)))) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsum_eq : (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / (q : ℝ))
          * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / (q : ℝ))))
      = (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
          (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / (q : ℝ)) *
          (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / (q : ℝ))) := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsum_eq, Work.FIArea5.S16.holoGaussian2d m hu ((ξ.1 : ℝ) / (q : ℝ))
    ((ξ.2 : ℝ) / (q : ℝ))]
  have hbase : (↑((ξ.1 : ℝ) / (q : ℝ)) + Complex.I * ↑((ξ.2 : ℝ) / (q : ℝ)) : ℂ)
      = (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (q : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_div]
    push_cast
    ring
  have hexp : -Real.pi * ((↑((ξ.1 : ℝ) / (q : ℝ)) : ℂ) ^ 2
        + (↑((ξ.2 : ℝ) / (q : ℝ)) : ℂ) ^ 2) / (u : ℂ)
      = -Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) / ((u : ℂ) * (q : ℂ) ^ 2)) := by
    rw [Complex.ofReal_div, Complex.ofReal_div]
    push_cast
    field_simp
  rw [hbase, hexp]
  ring

theorem allZPerXi (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (m : ℕ) {u : ℝ} (hu : 0 < u)
    (hq : 0 < Work.FIPlan.gnorm M) (ξ : ℤ × ℤ) :
    (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        (chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
          ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))
            * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ)))))
      = chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
          ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((Work.FIPlan.gnorm M : ℕ) : ℂ))) ^ m *
            Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
              / ((u : ℂ) * (((Work.FIPlan.gnorm M : ℕ) : ℂ)) ^ 2)))) := by
  rw [show (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        (chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
          ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))
            * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ)))))
      = chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
        (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))
            * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))))
      from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring)]
  rw [allZPerXi_core (Work.FIPlan.gnorm M) hq m hu ξ]
  ring

end Work.FIArea6Hecke
