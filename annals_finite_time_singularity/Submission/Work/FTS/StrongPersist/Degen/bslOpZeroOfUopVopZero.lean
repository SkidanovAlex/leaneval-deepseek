import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `U(Ξ) = V(Ξ) = 0` on the open quadrant implies `L(Ξ) = 0`

The statement and the proof below only involve the vocabulary of `Work.Construction`
(`Uop`, `Vop`), `Work.Elliptic` (`bslOp`, `Lzero`) and `Work.Spaces` (`pz`, `pth`, `pzIter`), so
this module is deliberately *self-contained*: it does not import the area's `StrongPersist.Defs`
(it is not used here), and therefore its verification does not depend on that file's state.

The elliptic operator `L = bslOp α` of (PolarBSL) annihilates every function in the joint kernel
of the two first-order operators

`U(Ξ) = -3Ξ - α z ∂_zΞ`,  `V(Ξ) = ∂_θΞ - tan θ · Ξ`.

The reason is the *exact algebraic identity*

`L(Ξ) = α z · ∂_z(U(Ξ)) + 2 U(Ξ) - ∂_θ(V(Ξ))`

(i.e. `L(Ξ) = α z pz(Uop α Ξ) + 2 Uop α Ξ - pth(Vop Ξ)`).
Indeed `Lzero(Ξ) = -∂_θ(V(Ξ)) - 6Ξ` because the two second-order angular terms cancel against
`∂_θ(V Ξ)`, and the two radial terms of `L` are `α z ∂_z(U Ξ) + 2U Ξ + 6Ξ`.

The statement is *not* vacuous: for every `α > 0` and every constant `c`, the function
`Ξ z θ = c z^{-3/α} / cos θ` satisfies `U Ξ = V Ξ = 0` on the open quadrant `(0,∞) × (0,π/2)`
(it is the general solution, the equations being a first-order system), and `L(Ξ) = 0`.

Both `U` and `V` vanish on the *whole* open quadrant, so the derivatives occurring in the
identity are *not* extra hypotheses: each of the three quantities `U Ξ`, `V Ξ`, `∂_z(U Ξ)`,
`∂_θ(V Ξ)` is a derivative of a function which is identically zero on a neighbourhood of the
point, hence zero.  Concretely, `∂_z(U Ξ)` is computed from the first-order equation
`∂_zΞ = -3Ξ/(α z)` (valid on the quadrant) by the quotient rule, which is why only the
*first* order differentiability `hdiffz`, `hdiffθ` of the statement is needed.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.Degen

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Pointwise consequences of `U(Ξ) = 0` on the open quadrant -/

/-- From `Uop α Ξ = 0` on the open quadrant: `∂_zΞ = -3Ξ/(α z)`. -/
private lemma pz_eq_of_Uop {α : ℝ} (hα : 0 < α) {Ξ : ℝ → ℝ → ℝ}
    (hU : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α Ξ z θ = 0)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pz Ξ z θ = -3 * Ξ z θ / (α * z) := by
  have h0 : -3 * Ξ z θ - α * z * Work.Spaces.pz Ξ z θ = 0 := by
    simpa only [Work.Construction.Uop] using hU z θ hz hθ1 hθ2
  have hne : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
  have h1 : α * z * Work.Spaces.pz Ξ z θ = -3 * Ξ z θ := by linarith
  rw [eq_div_iff hne]
  rw [mul_comm (Work.Spaces.pz Ξ z θ) (α * z)]
  exact h1

/-- From `Uop α Ξ = 0` on the open quadrant: `∂_z²Ξ = (9+3α)Ξ/(α²z²)`.

`∂_z²Ξ` is the derivative of `z' ↦ ∂_zΞ(z')`, and on the open quadrant that function agrees with
`z' ↦ -3Ξ/(α z')` (`pz_eq_of_Uop`), whose derivative at `z` is computed by the quotient rule. -/
private lemma pzIter_two_eq_of_Uop {α : ℝ} (hα : 0 < α) {Ξ : ℝ → ℝ → ℝ}
    (hU : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α Ξ z θ = 0)
    (hdiffz : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun z' => Ξ z' θ) z)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pzIter 2 Ξ z θ = (9 + 3 * α) * Ξ z θ / (α ^ 2 * z ^ 2) := by
  have hne : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
  have hpz : deriv (fun z' => Ξ z' θ) z = -3 * Ξ z θ / (α * z) :=
    pz_eq_of_Uop hα hU hz hθ1 hθ2
  -- on the open quadrant, `z' ↦ ∂_z Ξ(z')` agrees with the explicit quotient
  have hev : (fun z' => Work.Spaces.pz Ξ z' θ) =ᶠ[𝓝 z]
      (fun z' => -3 * Ξ z' θ / (α * z')) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)
      (fun z' hz' => pz_eq_of_Uop hα hU hz' hθ1 hθ2)
  have hderiv : deriv (fun z' => -3 * Ξ z' θ / (α * z')) z
      = ((-3 * deriv (fun z' => Ξ z' θ) z) * (α * z) - (-3 * Ξ z θ) * α) / (α * z) ^ 2 := by
    have hnum : HasDerivAt (fun z' => -3 * Ξ z' θ) (-3 * deriv (fun z' => Ξ z' θ) z) z :=
      (hdiffz z θ hz hθ1 hθ2).hasDerivAt.const_mul (-3)
    have hden : HasDerivAt (fun z' => α * z') α z := by
      simpa using (hasDerivAt_id z).const_mul α
    have hd := (hnum.div hden hne).deriv
    rw [show ((fun z' => -3 * Ξ z' θ) / (fun z' => α * z'))
        = (fun z' => -3 * Ξ z' θ / (α * z')) from rfl] at hd
    exact hd
  rw [show Work.Spaces.pzIter 2 Ξ z θ = deriv (fun z' => Work.Spaces.pz Ξ z' θ) z from rfl,
    hev.deriv_eq, hderiv, hpz]
  have hs : (α * z) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hs' : α ^ 2 * z ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ## Pointwise consequence of `V(Ξ) = 0` on the open quadrant -/

/-- From `Vop Ξ = 0` on the open quadrant: `Lzero Ξ = -6Ξ`.

The two second-order angular terms of `Lzero` are `-∂_θ²Ξ + ∂_θ(tan θ · Ξ)`, and they cancel
against `∂_θ(∂_θΞ - tan θ · Ξ) = ∂_θ(V Ξ)`: on the quadrant `∂_θΞ` agrees with
`tan θ · Ξ`, so `∂_θ²Ξ = ∂_θ(tan θ · Ξ)`.  The agreement is an equality of the two functions on
a neighbourhood of `θ` (the whole interval `(0,π/2)`), so it passes to the derivatives —
`Filter.EventuallyEq.deriv_eq` — with no second-order differentiability hypothesis. -/
private lemma Lzero_eq_of_Vop {Ξ : ℝ → ℝ → ℝ}
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Vop Ξ z θ = 0)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Elliptic.Lzero Ξ z θ = -6 * Ξ z θ := by
  have hev : (fun θ' => Work.Spaces.pth Ξ z θ') =ᶠ[𝓝 θ]
      (fun θ' => Real.tan θ' * Ξ z θ') :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hθ1 hθ2) (fun θ' hθ' => by
      have hv := hV z θ' hz hθ'.1 hθ'.2
      simp only [Work.Construction.Vop, Work.Spaces.pth] at hv ⊢
      linarith)
  have hderiv := hev.deriv_eq
  simp only [Work.Elliptic.Lzero]
  rw [show Work.Spaces.pthIter 2 Ξ z θ = deriv (fun θ' => Work.Spaces.pth Ξ z θ') θ from rfl]
  rw [show Work.Spaces.pth (fun z θ' => Real.tan θ' * Ξ z θ') z θ
        = deriv (fun θ' => Real.tan θ' * Ξ z θ') θ from rfl]
  rw [hderiv]
  ring

/-! ## The main theorem -/

theorem bslOpZeroOfUopVopZero {α : ℝ} (hα : 0 < α) {Ξ : ℝ → ℝ → ℝ}
    (hU : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α Ξ z θ = 0)
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Vop Ξ z θ = 0)
    (hdiffz : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → DifferentiableAt ℝ (fun z' => Ξ z' θ) z)
    (hdiffθ : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → DifferentiableAt ℝ (fun θ' => Ξ z θ') θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ξ z θ = 0 := by
  intro z θ hz hθ1 hθ2
  have hLzero : Work.Elliptic.Lzero Ξ z θ = -6 * Ξ z θ :=
    Lzero_eq_of_Vop hV hz hθ1 hθ2
  have hZ : -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ξ z θ
      - (α * (5 + α) * z) * Work.Spaces.pz Ξ z θ = 6 * Ξ z θ := by
    have h1 := pzIter_two_eq_of_Uop hα hU hdiffz hz hθ1 hθ2
    have h2 := pz_eq_of_Uop hα hU hz hθ1 hθ2
    have hne : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
    have hs : α ^ 2 * z ^ 2 ≠ 0 := by positivity
    rw [h1, h2]
    field_simp
    ring
  simp only [Work.Elliptic.bslOp]
  rw [hLzero]
  linarith

end Work.FTS.StrongPersist.Degen
