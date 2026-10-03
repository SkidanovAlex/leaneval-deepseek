/-
# `Submission.Work.FIArea6.S16ErrTwo.Defs` — a self-contained §16 error vocabulary

The §16 error term is `2 Σ_{d ≤ X} (φ(d)/d) ‖Vd d − MainSum X d‖`.  This file fixes the four
masses into which the pair sum `Vd − MainSum` splits according to the size of `|Δ(z₁,z₂)|` and the
coprimality of the pair, together with the two pointwise bounds on the summand
`logFac6 z₁ z₂ − logFac6Series z₁ z₂ (Kcut X)` that the split consumes.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6.S16ErrTwo.Base
import Submission.Work.FIArea6.S16_elem_alt
import Submission.Work.FIArea6b.sector_tau_sum
import Submission.Work.FIArea6.card_dvd_delta_fiber_near_le

set_option autoImplicit false

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The near-diagonal threshold `M = 2πN/X` of (16.5)/(16.6) with `H = X`. -/
def Mthr (Pa : Work.FITop.Params) (X : ℕ) : ℝ := 2 * Real.pi * Pa.N / (X : ℝ)

/-- The pointwise constant of the §16 error: both `|logFac6|` (on the support) and
`‖logFac6Series‖`, and their sum, are dominated by `Bc Pa = 16 + 16 log(2+N)`. -/
def Bc (Pa : Work.FITop.Params) : ℝ := 16 + 16 * Real.log (2 + Pa.N)

/-- The diagonal mass: the pairs of the box with `Δ(z₁,z₂) = 0`, weighted by `‖βz₁‖‖βz₂‖`. -/
def diagMass (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.Delta z1 z2 = 0 then ‖β z1‖ * ‖β z2‖ else 0)

/-- The near-diagonal mass at the modulus `4d`. -/
def nearMass (Pa : Work.FITop.Params) (X : ℕ) (d : ℕ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if 0 < Work.FIPlan.absDelta z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Mthr Pa X
      then ‖β z1‖ * ‖β z2‖ else 0)

/-- The far piece at the modulus `4d`, weighted by the truncation error `8N/(X³|Δ|)`. -/
def farMass (Pa : Work.FITop.Params) (X : ℕ) (d : ℕ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      then ‖β z1‖ * ‖β z2‖ * (8 * Pa.N / ((Kcut X : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)))
      else 0)

/-- The non-coprime mass at the modulus `4d`. -/
def ncMass (Pa : Work.FITop.Params) (d : ℕ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if ¬ Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      then ‖β z1‖ * ‖β z2‖ else 0)

/-! ## 1. Elementary facts -/

/-- `|Δ(z₂,z₁)| = |Δ(z₁,z₂)|`. -/
lemma absDelta_comm (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z2 z1 = Work.FIPlan.absDelta z1 z2 := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, Work.FIArea6.Delta_eq_neg]
  exact Int.natAbs_neg _

lemma Bc_nonneg (Pa : Work.FITop.Params) : 0 ≤ Bc Pa := by
  rw [Bc]
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have h : 0 ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith)
  linarith

lemma Mthr_nonneg (Pa : Work.FITop.Params) (X : ℕ) : 0 ≤ Mthr Pa X := by
  rw [Mthr]
  have hN1 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  positivity

end

end Work.FIArea6.S16ErrTwo
