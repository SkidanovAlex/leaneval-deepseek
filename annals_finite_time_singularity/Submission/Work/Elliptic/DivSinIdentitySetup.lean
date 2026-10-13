/-
Copyright: work module for the Elgindi finite-time singularity project.

# The integration-by-parts identity `DivSinIdentityA`: vocabulary

For a smooth angular slice `h` vanishing at `θ = 0, π/2`, put `u = SinQ h = h / sin 2θ`.
The identity proved in `Work.Elliptic.DivSinIdentityA` is

  `∫_0^{π/2} h'(θ)² sin(2θ)^{-η} dθ
     = ∫_0^{π/2} u'(θ)² sin(2θ)^{2-η} dθ
       + 4η ∫_0^{π/2} cos²(2θ) u(θ)² sin(2θ)^{-η} dθ
       + 4 ∫_0^{π/2} sin(2θ)^{2-η} u(θ)² dθ`.

Its proof is the observation that the difference of the two integrands is the derivative of the
explicit primitive

  `PhiA h θ = 2 cos(2θ) sin(2θ)^{1-η} u(θ)² = 2 cos(2θ) h(θ)² sin(2θ)^{-(1+η)}`,

which vanishes at both endpoints.  This module fixes the four integrands `F1A … F4A`, the
primitive `PhiA` and its explicit derivative `dPhiA`, together with the elementary trigonometric
bounds used by every one of them.  The analytic ingredients live in the separate modules
`DivSinIdIntegr` (integrability on `Iθ`), `DivSinIdPhiTendsto` (the vanishing at the endpoints),
`DivSinIdPhiDeriv` (the derivative of `PhiA`) and `DivSinIdPointwise` (the pointwise identity).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.DivSinBddDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## The four integrands and the primitive -/

/-- The integrand of the left-hand side of `DivSinIdentityA`. -/
def F1A (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta)

/-- The first integrand of the right-hand side of `DivSinIdentityA`. -/
def F2A (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv (SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)

/-- The second integrand of the right-hand side of `DivSinIdentityA`. -/
def F3A (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.cos (2 * θ)) ^ 2 * (SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta)

/-- The third integrand of the right-hand side of `DivSinIdentityA`. -/
def F4A (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) * (SinQ h θ) ^ 2

/-- The primitive whose derivative is `F1A - F2A - 4η F3A - 4 F4A`:
`PhiA h θ = 2 cos(2θ) sin(2θ)^{1-η} (SinQ h θ)² = 2 cos(2θ) h(θ)² sin(2θ)^{-(1+η)}`
(the second form extends continuously by `0` at the endpoints). -/
def PhiA (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => 2 * Real.cos (2 * θ) * (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- The explicit derivative of `PhiA h` on `(0, π/2)`. -/
def dPhiA (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  -4 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) * (SinQ h θ) ^ 2
    + 4 * (1 - Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) * (SinQ h θ) ^ 2
    + 4 * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
        * (SinQ h θ) * deriv (SinQ h) θ

/-! ## Elementary facts -/

/-- `SinQ` and the `htU` of the Hardy calculus are the same function. -/
lemma SinQ_eq_htU (h : ℝ → ℝ) : SinQ h = htU h := rfl

theorem eta_pos' : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos

theorem eta_lt_one' : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one

theorem eta_nonneg' : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg

theorem one_add_eta_pos : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [eta_pos']

theorem one_sub_eta_pos : (0 : ℝ) < 1 - Work.Spaces.eta := by linarith [eta_lt_one']

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) ≠ 0` on `(0, π/2)`. -/
theorem sin_two_ne_zero' {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (sin_two_pos hθ)

/-- Jordan's inequality on the left half-interval: `sin (2θ) ≥ (4/π) θ` for `0 < θ < π/4`. -/
theorem sin_two_ge_left {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 4)) :
    4 / π * θ ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ π / 2 := by linarith [hθ.2, Real.pi_pos]
  have h := Real.mul_le_sin h1 h2
  rwa [show (2 : ℝ) / π * (2 * θ) = 4 / π * θ by ring] at h

/-- Jordan's inequality on the right half-interval: `sin (2θ) ≥ (4/π) (π/2 - θ)`
for `π/4 < θ < π/2`. -/
theorem sin_two_ge_right {θ : ℝ} (hθ : θ ∈ Set.Ioo (π / 4) (π / 2)) :
    4 / π * (π / 2 - θ) ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * (π / 2 - θ) := by linarith [hθ.2, Real.pi_pos]
  have h2 : 2 * (π / 2 - θ) ≤ π / 2 := by linarith [hθ.1, Real.pi_pos]
  have h := Real.mul_le_sin h1 h2
  have heq : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
    rw [show 2 * θ = π - 2 * (π / 2 - θ) by ring, Real.sin_pi_sub]
  rw [heq]
  rwa [show (2 : ℝ) / π * (2 * (π / 2 - θ)) = 4 / π * (π / 2 - θ) by ring] at h

/-- `sin (2θ) ≤ 2θ` on `(0, π/4)`. -/
theorem sin_two_le_left {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 4)) :
    Real.sin (2 * θ) ≤ 2 * θ := by
  have h1 : 0 < 2 * θ := by linarith [hθ.1]
  exact le_of_lt (Real.sin_lt h1)

/-- `sin (2θ) ≤ 2 (π/2 - θ)` on `(π/4, π/2)`. -/
theorem sin_two_le_right {θ : ℝ} (hθ : θ ∈ Set.Ioo (π / 4) (π / 2)) :
    Real.sin (2 * θ) ≤ 2 * (π / 2 - θ) := by
  have h1 : 0 < 2 * (π / 2 - θ) := by linarith [hθ.2]
  have h2 := Real.sin_lt h1
  have heq : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
    rw [show 2 * θ = π - 2 * (π / 2 - θ) by ring, Real.sin_pi_sub]
  rw [heq]; exact le_of_lt h2

/-- Almost every point of `Iθ` is an interior point of `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  simp only [Work.Spaces.Iθ]
  rw [Measure.restrict_congr_set
    (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]
  exact self_mem_ae_restrict measurableSet_Ioo

end Work.Elliptic
