/-
# `Work.FTS.BSSwirl.Defs` — the Biot–Savart law for swirl vorticity

This is the vocabulary of the `BSSwirl` area of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

The area proves **item 7a of the lead's design `FTS_PHYS_BRIDGE.md` §1**: for a compactly
supported `α`-Hölder *swirl* vorticity `ω = f(r,z) • e_θ`,

  `∇ × (BS ω) = ω`   and   `div (BS ω) = 0`   everywhere on `ℝ³`,

where `BS` is the Newtonian-potential Biot–Savart operator `Work.LWP.biotSavart`.  This replaces
the *false* named input `Work.LWP.BiotSavartLaw` (see `FTS_NOTBSL.lean.txt`) by a theorem in the
restricted (honest) setting in which the physical reconstruction uses it.

## Contents of this module

* `swirlField f` — the swirl field `x ↦ f (r x) (z x) • e_θ(x)` with `r`, `z` the cylindrical
  coordinates `Work.Cyl.radial`, `Work.Cyl.axial`;
* `swirlWeight f` — the radial weight `f(r,z)/r`, so that
  `swirlField f x = swirlWeight f x • angularVec x` (`swirlField_eq_smul_angularVec`), the form in
  which the rotation-invariance of the swirl field is expressed;
* `newtonPotential ω` — the vector Newtonian potential `A ω x = (4π)⁻¹ ∫ ‖x-y‖⁻¹ • ω y dy`, whose
  curl is the Biot–Savart field;
* `WeakDivFree ω` — the weak (distributional) form of `div ω = 0`, i.e. `∫ ⟪ω, ∇k⟫ = 0` for every
  smooth compactly supported test function `k`.  This is the hypothesis under which the curl half
  of the Biot–Savart law holds (the `div` half needs nothing);
* `BiotSavartSwirl` — the statement of item 7a of the design, verbatim.

Everything is written against the *fixed* definitions of `ChallengeDeps.lean`
(`FiniteTimeSingularity.vorticity`, `FiniteTimeSingularity.div`) and the existing workspace
vocabulary (`Work.LWP.biotSavart`, `Work.Cyl`); nothing is redefined.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.LWP.Defs
import Submission.Work.Cyl.norm_angularVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

/-- `ℝ³`, the Euclidean space with the standard basis indexed by `Fin 3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## The swirl field -/

/-- **The swirl (purely azimuthal) vector field** `ω x = f (r x) (z x) • e_θ(x)`, where `r` is the
distance to the `x₃`-axis (`Work.Cyl.radial`) and `z` the axial coordinate (`Work.Cyl.axial`).
`Work.Cyl.eTheta` vanishes on the axis, so `swirlField f` vanishes on the axis for every `f`; in
particular no regularity of `f` at `r = 0` is needed. -/
def swirlField (f : ℝ → ℝ → ℝ) (x : R3) : R3 :=
  f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x

@[simp] theorem swirlField_apply (f : ℝ → ℝ → ℝ) (x : R3) :
    swirlField f x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x := rfl

/-- **The radial weight of a swirl field**, `f(r,z)/r`.  Away from the axis the swirl field is
`swirlWeight f x • angularVec x`, i.e. `(f(r,z)/r) • (x₀,x₁,0)`; the weight is the
rotation-invariant factor (see `swirlWeight_comp`). -/
def swirlWeight (f : ℝ → ℝ → ℝ) (x : R3) : ℝ :=
  f (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x

/-- **The swirl field as a rotation-invariant weight times the polynomial field
`angularVec x = (-x₁,x₀,0)`.**  This is the form used by the rotation argument proving that a
swirl field is weakly divergence-free. -/
theorem swirlField_eq_smul_angularVec (f : ℝ → ℝ → ℝ) (x : R3) :
    swirlField f x = swirlWeight f x • Work.Cyl.angularVec x := by
  rw [swirlField, swirlWeight, Work.Cyl.eTheta, smul_smul]
  have : f (Work.Cyl.radial x) (Work.Cyl.axial x) * (1 / Work.Cyl.radial x)
      = f (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x := by
    rw [div_eq_mul_inv]; ring
  rw [this]

/-- The angular unit vector has norm at most one (it vanishes on the axis). -/
theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  rw [Work.Cyl.eTheta]
  by_cases hr : Work.Cyl.radial x = 0
  · rw [hr, one_div, _root_.inv_zero, zero_smul, norm_zero]
    norm_num
  · have hpos : 0 < 1 / Work.Cyl.radial x :=
      one_div_pos.mpr (lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, Work.Cyl.norm_angularVec x,
      div_mul_cancel₀ _ hr]

/-- The norm of a swirl field is at most the absolute value of the profile.  In particular a
swirl field whose profile is bounded by `M` is bounded by `M`. -/
theorem norm_swirlField_le (f : ℝ → ℝ → ℝ) (x : R3) :
    ‖swirlField f x‖ ≤ |f (Work.Cyl.radial x) (Work.Cyl.axial x)| := by
  rw [swirlField, norm_smul]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_eTheta_le_one x)

/-- **Rotation invariance of the swirl weight.**  If a linear isometry equivalence preserves the
cylindrical coordinates `r` and `z`, then it preserves the weight `f(r,z)/r`; in particular the
rotations about the `x₃`-axis do. -/
theorem swirlWeight_comp (f : ℝ → ℝ → ℝ) (R : R3 ≃ₗᵢ[ℝ] R3)
    (hr : ∀ x, Work.Cyl.radial (R x) = Work.Cyl.radial x)
    (hz : ∀ x, Work.Cyl.axial (R x) = Work.Cyl.axial x) (x : R3) :
    swirlWeight f (R x) = swirlWeight f x := by
  rw [swirlWeight, swirlWeight, hr x, hz x]

/-! ## The Newtonian potential and the weak divergence-free condition -/

/-- **The vector Newtonian potential** `A ω x = (4π)⁻¹ ∫ ‖x-y‖⁻¹ • ω y dy`.  Its curl is the
Biot–Savart field `Work.LWP.biotSavart ω` (`biotSavart_eq_vorticity_newtonPotential`), so that the
Biot–Savart law becomes the classical pair of identities `ΔA = -ω` and `∇·A = 0` for the
potential. -/
def newtonPotential (ω : R3 → R3) (x : R3) : R3 :=
  (4 * Real.pi)⁻¹ • ∫ y, (‖x - y‖)⁻¹ • ω y


@[simp] theorem newtonPotential_apply (ω : R3 → R3) (x : R3) :
    newtonPotential ω x = (4 * Real.pi)⁻¹ • ∫ y, (‖x - y‖)⁻¹ • ω y := rfl

/-- **The candidate Fréchet derivative of the Newtonian potential**, namely

  `h ↦ (4π)⁻¹ ∫ ‖x-y‖⁻³ • (⟪y-x,h⟫ • ω y) dy`.

It is the derivative of `newtonPotential ω` wherever `ω` is bounded and compactly supported
(`Work.FTS.BSSwirl.hasFDerivAt_newtonPotential`). -/
def potDeriv (ω : R3 → R3) (x : R3) : R3 →L[ℝ] R3 :=
  (4 * Real.pi)⁻¹ • ∫ y, (‖x - y‖ ^ (3 : ℕ))⁻¹ •
    (innerSL ℝ (y - x)).smulRight (ω y)

/-- **Weak (distributional) divergence-free condition.**  `ω` has zero distributional divergence:
`∫ ⟪ω x, ∇k x⟫ dx = 0` for every smooth compactly supported scalar test function `k`.  This is the
exact form of `div ω = 0` needed by the integration-by-parts proof of the curl half of the
Biot–Savart law.  For the physical application `ω` is a swirl field, for which it is proved in
`Work.FTS.BSSwirl.SwirlWeak`. -/
def WeakDivFree (ω : R3 → R3) : Prop :=
  ∀ k : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
    ∫ x, inner ℝ (ω x) (∇ k x) = 0

/-- The weak divergence-free condition, in the equivalent `fderiv` form. -/
theorem weakDivFree_iff (ω : R3 → R3) :
    WeakDivFree ω ↔ ∀ k : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
      ∫ x, (fderiv ℝ k x) (ω x) = 0 := by
  constructor
  · intro h k hk hsupp
    have h' := h k hk hsupp
    rw [← h']
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_gradient_right]
    simp
  · intro h k hk hsupp
    have h' := h k hk hsupp
    rw [← h']
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_gradient_right]
    simp

/-! ## The statement of item 7a -/

/-- **Item 7a of the lead's design (`FTS_PHYS_BRIDGE.md` §1).**  For every compactly supported
`α`-Hölder swirl vorticity `ω = f(r,z) • e_θ` with `0 < α < 1`, the Biot–Savart velocity inverts
the curl and is divergence-free everywhere:

  `∇ × (BS ω) = ω`   and   `div (BS ω) = 0`   on `ℝ³`.

The proof is `Work.FTS.BSSwirl.biotSavartSwirl`. -/
def BiotSavartSwirl : Prop :=
  ∀ (f : ℝ → ℝ → ℝ) (C α : ℝ≥0) (R : ℝ), 0 < (α : ℝ) → (α : ℝ) < 1 →
    let ω := swirlField f
    HolderWith C α ω → (∀ x, ω x ≠ 0 → ‖x‖ ≤ R) →
    (∀ x, vorticity (Work.LWP.biotSavart ω) x = ω x) ∧
      ∀ x, div (Work.LWP.biotSavart ω) x = 0

end

end Work.FTS.BSSwirl
