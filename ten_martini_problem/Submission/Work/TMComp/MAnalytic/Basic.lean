import Mathlib
import Submission.Work.TMContract.Defs

/-!
# C9 (`P_mAnalytic`): the invariant section of the almost Mathieu cocycle

This module holds the vocabulary of the proof of the frozen component C9
(`Work.TMContract.P_mAnalytic`): the invariant section `m` of the almost Mathieu cocycle
(AJ §2.3, (2.6)), its analyticity hypotheses, and the algebra of the section equation.

The route (AJ Thm 3.1, 3.2 and (4.11)–(4.13)) is:

1. Kotani theory (component C8) + Bourgain–Jitomirskaya (component C7) produce the invariant
   section `m : (a,b) × ℝ → ℍ` of the cocycle `S_{λ,E}(x) = tmC λ E x`, jointly real-analytic.
2. From `m` one builds AJ's conjugating matrix `C_E(x) =ᵃ [[1/√σ, −β/√σ],[0,√σ]]` where
   `m = β + iσ`; then `C_E(x+α) S_E(x) C_E(x)⁻¹ ∈ SO(2)` and one reads off the angle `φ`,
   producing the conclusion of C9.

Everything in this file is proved; the analytic input (step 1) is isolated in
`AnalyticSection` so that the construction (step 2) can be proved independently of Kotani
theory. -/

open LeanEval.Analysis.TenMartini
open Work.TMContract Set Filter Topology

noncomputable section

namespace Work.TMComp.MAnalytic

/-- The `(0,0)` coefficient `a = E − 2λ cos 2πx` of the transfer matrix `tmC λ E x`. -/
def coeff (lam : ℝ) (E x : ℝ) : ℝ := E - 2 * lam * Real.cos (2 * Real.pi * x)

theorem coeff_eq (lam E x : ℝ) : (tmC lam (E : ℂ) x) 0 0 = ((coeff lam E x : ℝ) : ℂ) := by
  simp [tmC, coeff]

/-- The invariant-section equation of the almost Mathieu cocycle at the point `(E,x)`, in the
division-free form `a·m − 1 = m·m(·+α)` with `a = coeff λ E x`:
for `m` with non-zero (e.g. upper half plane) values this is the Möbius relation
`mob (tmC λ E x) (m E x) = m E (x+α)` (AJ (2.6), (4.12)). -/
def SecEq (α lam : ℝ) (E x : ℝ) (m : ℝ → ℝ → ℂ) : Prop :=
  ((coeff lam E x : ℝ) : ℂ) * m E x - 1 = m E x * m E (x + α)

/-- The invariant section of the almost Mathieu cocycle on `(a,b) × ℝ`, with the regularity
supplied by Kotani theory (C8) and Bourgain–Jitomirskaya (C7): jointly real-analytic, values in
the upper half plane, 1-periodic in `x`, section equation. -/
structure AnalyticSection (α lam a b : ℝ) (m : ℝ → ℝ → ℂ) : Prop where
  /-- joint real-analyticity on `(a,b) × ℝ` -/
  analytic : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => m p.1 p.2) (Ioo a b ×ˢ univ)
  /-- values in the upper half plane -/
  im_pos : ∀ E ∈ Ioo a b, ∀ x, 0 < (m E x).im
  /-- 1-periodicity in `x` -/
  periodic : ∀ E x, m E (x + 1) = m E x
  /-- the section equation -/
  sec : ∀ E ∈ Ioo a b, ∀ x, SecEq α lam E x m

/-- The section equation as the Möbius relation (for non-zero `m`). -/
theorem secEq_iff_mob {α lam E x : ℝ} {m : ℝ → ℝ → ℂ} (hm : m E x ≠ 0) :
    SecEq α lam E x m ↔ mob (tmC lam (E : ℂ) x) (m E x) = m E (x + α) := by
  have htm : (tmC lam (E : ℂ) x) 0 0 = ((coeff lam E x : ℝ) : ℂ) := coeff_eq lam E x
  have h01 : (tmC lam (E : ℂ) x) 0 1 = -1 := by simp [tmC]
  have h10 : (tmC lam (E : ℂ) x) 1 0 = 1 := by simp [tmC]
  have h11 : (tmC lam (E : ℂ) x) 1 1 = 0 := by simp [tmC]
  rw [SecEq, mob, htm, h01, h10, h11, one_mul, add_zero, div_eq_iff hm,
    mul_comm (m E (x + α)) (m E x), sub_eq_add_neg]

section Algebra

variable {α lam E x : ℝ} {m : ℝ → ℝ → ℂ}

/-- Real part of the section equation. -/
theorem sec_re (h : SecEq α lam E x m) :
    coeff lam E x * (m E x).re - 1
      = (m E x).re * (m E (x + α)).re - (m E x).im * (m E (x + α)).im := by
  have h' : ((coeff lam E x : ℝ) : ℂ) * m E x - 1 = m E x * m E (x + α) := h
  have := congrArg Complex.re h'
  simpa only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using this

/-- Imaginary part of the section equation. -/
theorem sec_im (h : SecEq α lam E x m) :
    coeff lam E x * (m E x).im
      = (m E x).re * (m E (x + α)).im + (m E x).im * (m E (x + α)).re := by
  have h' : ((coeff lam E x : ℝ) : ℂ) * m E x - 1 = m E x * m E (x + α) := h
  have := congrArg Complex.im h'
  simpa only [Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero] using this

/-- Consequence of the section equation: `σ' (β² + σ²) = σ`, where `m = β + iσ`,
`m(·+α) = β' + iσ'`. -/
theorem sec_sigma (h : SecEq α lam E x m) :
    (m E (x + α)).im * ((m E x).re ^ 2 + (m E x).im ^ 2) = (m E x).im := by
  have h1 := sec_re h
  have h2 := sec_im h
  linear_combination (m E x).im * h1 - (m E x).re * h2

/-- Consequence of the section equation: `(a − β') (β² + σ²) = β`, where `a = coeff λ E x`,
`m = β + iσ`, `m(·+α) = β' + iσ'`. -/
theorem sec_beta (h : SecEq α lam E x m) :
    (coeff lam E x - (m E (x + α)).re) * ((m E x).re ^ 2 + (m E x).im ^ 2) = (m E x).re := by
  have h1 := sec_re h
  have h2 := sec_im h
  linear_combination (m E x).re * h1 + (m E x).im * h2

end Algebra

end Work.TMComp.MAnalytic
