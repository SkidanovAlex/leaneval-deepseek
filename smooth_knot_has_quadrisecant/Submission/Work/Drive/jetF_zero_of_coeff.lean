import Mathlib
import Submission.Work.Drive.knotPerturbDefs
import Submission.Work.Drive.jetDefs

/-!
# Fourier form of the six jet relations

`jetF p q r α β γ δ ε ζ k` is the complex number
`(α + i k β) e^{ikp} + (γ + i k δ) e^{ikq} + (ε + i k ζ) e^{ikr}`.

This file shows that if the real functional
`α·(value at p) + β·(derivative at p) + γ·(value at q) + δ·(derivative at q)
 + ε·(value at r) + ζ·(derivative at r)`
vanishes on each of the nine basis functions `trigBasis j` (equivalently: on every
trigonometric polynomial of degree at most `4`), then `jetF k = 0` for every integer
`k` with `|k| ≤ 4`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The cosine part of the Fourier relation. -/
def jetC (p q r : ℝ) (α β γ δ ε ζ : ℝ) (k : ℤ) : ℝ :=
  α * Real.cos ((k : ℝ) * p) - (k : ℝ) * β * Real.sin ((k : ℝ) * p)
    + γ * Real.cos ((k : ℝ) * q) - (k : ℝ) * δ * Real.sin ((k : ℝ) * q)
    + ε * Real.cos ((k : ℝ) * r) - (k : ℝ) * ζ * Real.sin ((k : ℝ) * r)

/-- The sine part of the Fourier relation. -/
def jetS (p q r : ℝ) (α β γ δ ε ζ : ℝ) (k : ℤ) : ℝ :=
  α * Real.sin ((k : ℝ) * p) + (k : ℝ) * β * Real.cos ((k : ℝ) * p)
    + γ * Real.sin ((k : ℝ) * q) + (k : ℝ) * δ * Real.cos ((k : ℝ) * q)
    + ε * Real.sin ((k : ℝ) * r) + (k : ℝ) * ζ * Real.cos ((k : ℝ) * r)

/-- The Fourier relation splits into its real and imaginary parts. -/
theorem jetF_eq_cossin (p q r α β γ δ ε ζ : ℝ) (k : ℤ) :
    jetF p q r α β γ δ ε ζ k
      = (jetC p q r α β γ δ ε ζ k : ℂ) + (jetS p q r α β γ δ ε ζ k : ℂ) * Complex.I := by
  rw [jetF, jetFc, jetExp_zpow p, jetExp_zpow q, jetExp_zpow r]
  simp only [jetC, jetS]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, add_zero, mul_one]
  · ring
  · ring

/-- The cosine part is even in the frequency. -/
theorem jetC_neg (p q r α β γ δ ε ζ : ℝ) (k : ℤ) :
    jetC p q r α β γ δ ε ζ (-k) = jetC p q r α β γ δ ε ζ k := by
  simp only [jetC, Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, neg_neg]
  ring

/-- The sine part is odd in the frequency. -/
theorem jetS_neg (p q r α β γ δ ε ζ : ℝ) (k : ℤ) :
    jetS p q r α β γ δ ε ζ (-k) = -jetS p q r α β γ δ ε ζ k := by
  simp only [jetS, Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, neg_neg]
  ring

/-- **Fourier form of the jet relations.**  If the six jet functionals are linearly dependent on the
degree-`4` trigonometric basis (`h`, coefficientwise), then the Fourier combination `jetF k`
vanishes for every `k` with `|k| ≤ 4`. -/
theorem jetF_zero_of_coeff (p q r : ℝ) (α β γ δ ε ζ : ℝ)
    (h : ∀ j : Fin 9, α * trigBasis j p + β * trigBasisD j p + γ * trigBasis j q
        + δ * trigBasisD j q + ε * trigBasis j r + ζ * trigBasisD j r = 0) :
    ∀ k : ℤ, -4 ≤ k → k ≤ 4 → jetF p q r α β γ δ ε ζ k = 0 := by
  have h0 : α + γ + ε = 0 := by
    have hh := h 0
    simpa [trigBasis, trigBasisD] using hh
  have hc1 : jetC p q r α β γ δ ε ζ 1 = 0 := by
    have h1 := h 1
    have h2 := h 2
    simp only [trigBasis, trigBasisD] at h1 h2
    simp only [jetC]
    norm_num
    linarith
  have hs1 : jetS p q r α β γ δ ε ζ 1 = 0 := by
    have h1 := h 1
    have h2 := h 2
    simp only [trigBasis, trigBasisD] at h1 h2
    simp only [jetS]
    norm_num
    linarith
  have hc2 : jetC p q r α β γ δ ε ζ 2 = 0 := by
    have h3 := h 3
    have h4 := h 4
    simp only [trigBasis, trigBasisD] at h3 h4
    simp only [jetC]
    norm_num
    linarith
  have hs2 : jetS p q r α β γ δ ε ζ 2 = 0 := by
    have h3 := h 3
    have h4 := h 4
    simp only [trigBasis, trigBasisD] at h3 h4
    simp only [jetS]
    norm_num
    linarith
  have hc3 : jetC p q r α β γ δ ε ζ 3 = 0 := by
    have h5 := h 5
    have h6 := h 6
    simp only [trigBasis, trigBasisD] at h5 h6
    simp only [jetC]
    norm_num
    linarith
  have hs3 : jetS p q r α β γ δ ε ζ 3 = 0 := by
    have h5 := h 5
    have h6 := h 6
    simp only [trigBasis, trigBasisD] at h5 h6
    simp only [jetS]
    norm_num
    linarith
  have hc4 : jetC p q r α β γ δ ε ζ 4 = 0 := by
    have h7 := h 7
    have h8 := h 8
    simp only [trigBasis, trigBasisD] at h7 h8
    simp only [jetC]
    norm_num
    linarith
  have hs4 : jetS p q r α β γ δ ε ζ 4 = 0 := by
    have h7 := h 7
    have h8 := h 8
    simp only [trigBasis, trigBasisD] at h7 h8
    simp only [jetS]
    norm_num
    linarith
  have hC : ∀ m : ℤ, 1 ≤ m → m ≤ 4 → jetC p q r α β γ δ ε ζ m = 0 := by
    intro m hm1 hm4
    interval_cases m <;> first | exact hc1 | exact hc2 | exact hc3 | exact hc4
  have hS : ∀ m : ℤ, 1 ≤ m → m ≤ 4 → jetS p q r α β γ δ ε ζ m = 0 := by
    intro m hm1 hm4
    interval_cases m <;> first | exact hs1 | exact hs2 | exact hs3 | exact hs4
  have hpos : ∀ m : ℤ, 1 ≤ m → m ≤ 4 → jetF p q r α β γ δ ε ζ m = 0 := by
    intro m hm1 hm4
    rw [jetF_eq_cossin, hC m hm1 hm4, hS m hm1 hm4]
    simp
  have hneg : ∀ m : ℤ, 1 ≤ m → m ≤ 4 → jetF p q r α β γ δ ε ζ (-m) = 0 := by
    intro m hm1 hm4
    rw [jetF_eq_cossin, jetC_neg, jetS_neg, hC m hm1 hm4, hS m hm1 hm4]
    simp
  intro k hk1 hk2
  rcases lt_trichotomy k 0 with hlt | heq | hgt
  · rw [← neg_neg k]
    exact hneg (-k) (by omega) (by omega)
  · rw [heq, jetF_eq_cossin]
    have hC0 : jetC p q r α β γ δ ε ζ 0 = 0 := by
      simp only [jetC]
      push_cast
      simp [h0]
    have hS0 : jetS p q r α β γ δ ε ζ 0 = 0 := by
      simp only [jetS]
      push_cast
      simp
    rw [hC0, hS0]
    simp
  · exact hpos k (by omega) hk2

end

end Work.Drive
