/-
# Vocabulary for the §6 model approximation (`mod-approx`) of Area A7

This module fixes the two *analytic* objects of the single-scale model approximation of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

namely the oscillatory integral `m̃_{N,ℝ}` of \eqref{mn-def} and the symbol difference
`M₀` of Proposition `mod-approx`, together with the discrete average it compares with.

The content of the Proposition is the estimate of `M0` below: the difference between the discrete
average `E_{n ∈ [N]} e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n)) 1_{n>N/2}` and the product
`m_Ẑ(α₁,α₂) m̃_{N,ℝ}(ξ₁,ξ₂)` of the arithmetic symbol with the oscillatory integral is
`O(q² (1 + (2^{k₁}+2^{dk₂})²/N) / N)`, where `q` is any period of the arithmetic characters
`n ↦ e(α₁n+α₂P(n))` (i.e. `q • α₁ = q • α₂ = 0`).  This is the *sharp* form of the paper's
estimate: the paper's `2^{O(max(2^{ρl},s))} N^{-1}` hides a factor `2^{O(s)}` (`s` the continuous
scale) which the weight `modelWeight A ρ l₁ l₂ k₁ k₂ = (1+L)^A 2^{A 2^{ρL}}` cannot absorb; the
global (composite-trapezoid) argument below removes it.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- **The oscillatory integral `m̃_{N,ℝ}` of §6** (the paper's \eqref{mn-def}):
`m̃_{N,ℝ}(ξ₁,ξ₂) = ∫_{1/2}^1 e(ξ₁ N t + ξ₂ P(Nt)) dt`, `e(x) = ee x = exp(2πix)`. -/
noncomputable def mTilde (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) : ℂ :=
  ∫ t in (1/2 : ℝ)..1, ee (ξ₁ * (N : ℝ) * t + ξ₂ * PevalR P ((N : ℝ) * t))

/-- The summand of the discrete average defining `M₀`: the character
`n ↦ e(α₁ n + α₂ P(n)) e(ξ₁ n + ξ₂ P(n))`, with the arithmetic characters written in the
`fourier` convention of the Ionescu--Wainger framework. -/
noncomputable def momPhase (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ)
    (n : ℤ) : ℂ :=
  fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂
    * ee (ξ₁ * (n : ℝ) + ξ₂ * PevalR P (n : ℝ))

/-- **The discrete average** `E_{n ∈ [N]} e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n)) 1_{n>N/2}` of Proposition
`mod-approx`. -/
noncomputable def weylAvg (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)

/-- **The symbol difference `M₀` of Proposition `mod-approx`**:
`M₀ = E_{n∈[N]}e(α₁n+α₂P(n))e(ξ₁n+ξ₂P(n))1_{n>N/2} − m_Ẑ(α₁,α₂) m̃_{N,ℝ}(ξ₁,ξ₂)`, for a modulus
`q` that kills `α₁` and `α₂` (so that `q` is a period of the arithmetic characters). -/
noncomputable def M0 (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) : ℂ :=
  weylAvg P N α₁ α₂ ξ₁ ξ₂ - mZ P q α₁ α₂ * mTilde P N ξ₁ ξ₂

end

end Work.KMTAreas.A7
