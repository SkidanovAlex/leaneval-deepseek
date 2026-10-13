/-
Interior regularity (`bslOp_interiorSmooth`): the strip model.

This file fixes the translation of the weak formulation of `bslOp α Ψ = F` into an equation
for the *compactly supported unknown* `V` on `E2 = EuclideanSpace ℝ (Fin 2)`, in the coordinates
`s = (1/α) log z`, `θ`.

Concretely, with `u = Ψ · ω`, `ω = z^((5+α)/α) cos θ`:

* the change of variables `z = exp (α s)` turns the principal part `-α²z²∂_zz - α(5+α)z∂_z` into
  `-∂_ss - 5 ∂_s`, so that `bslOp α φ` computed at `(exp (α s), θ)` equals

      Kop ψ = -∂_ss ψ - ∂_θθ ψ - 5 ∂_s ψ + tan θ · ∂_θ ψ + (tan²θ - 5) ψ

  for `φ (z,θ) = ψ ((1/α) log z, θ)`;
* the unknown of the resulting equation is `V := α z u` (which is one Jacobian factor times `u`),
  and the source is `G := α z g`, `g = F ω`;
* the transpose of `Kop` is the operator `-Δ - tan θ ∂_θ + 5 ∂_s - 6`, i.e. the weak identity

      ∀ ψ, ∫ V · Kop ψ = ∫ G · ψ

  is equivalent to the distributional equation `Δ V = 5 ∂_s V - tan θ ∂_θ V - 6 V - G`.

Everything below is stated for functions on `E2 = EuclideanSpace ℝ (Fin 2)` (`Fin 2 → ℝ`),
with `x 0` the `s`-coordinate and `x 1` the `θ`-coordinate.  Directional derivatives are
`lineDeriv ℝ f x e`; `e0`, `e1` are the coordinate unit vectors.  `Δ` is Mathlib's Laplacian
(on functions and on tempered distributions), which agrees with `∂_{e0}∂_{e0} + ∂_{e1}∂_{e1}`.
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform Filter Set
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology LineDeriv Laplacian

namespace Work.EllipticEst.InteriorRegularity

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-- The two-dimensional Euclidean space used throughout. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate direction `e₀` (`s`-direction). -/
def e0 : E2 := EuclideanSpace.basisFun (Fin 2) ℝ 0

/-- The second coordinate direction `e₁` (`θ`-direction). -/
def e1 : E2 := EuclideanSpace.basisFun (Fin 2) ℝ 1

/-- The strip `{0 < θ < π/2}` in the `(s,θ)`-plane. -/
def stripE : Set E2 := {x : E2 | x 1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}

/-- The `s`-coordinate. -/
def Sc (x : E2) : ℝ := x 0

/-- The `θ`-coordinate. -/
def Th (x : E2) : ℝ := x 1

/-- Reinterpret a curried function as a function on `E2`. -/
def curry (F : ℝ → ℝ → ℝ) : E2 → ℝ := fun x => F (x 0) (x 1)

/-- Complex valued version of `curry`. -/
def curryC (F : ℝ → ℝ → ℂ) : E2 → ℂ := fun x => F (x 0) (x 1)

/-- The point of `E2` with coordinates `(s, θ)`. -/
def coords (s θ : ℝ) : E2 :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then s else θ)

theorem curryC_curry'_apply (F : ℝ → ℝ → ℂ) (s θ : ℝ) : curryC F (coords s θ) = F s θ := by
  simp [curryC, coords]

/-- Complexification of a real valued function. -/
def cplx {E : Type*} (f : E → ℝ) : E → ℂ := fun x => (f x : ℂ)

/-- The directional derivative in the `e₀` direction. -/
def d0 (f : E2 → ℂ) : E2 → ℂ := fun x => lineDeriv ℝ f x e0

/-- The directional derivative in the `e₁` direction. -/
def d1 (f : E2 → ℂ) : E2 → ℂ := fun x => lineDeriv ℝ f x e1

/-- The second order operator `Kop` transported to `E2`: for `ψ` a test function,
`Kop ψ = -∂_ss ψ - ∂_θθ ψ - 5 ∂_s ψ + tan θ ∂_θ ψ + (tan² θ - 5) ψ`.

This is `bslOp α φ` evaluated at `(exp (α s), θ)` when `φ (z,θ) = ψ ((1/α) log z, θ)`,
as a function of the strip coordinates; see `Vfun`, `Gfun` and `StripWeak` below. -/
def Kop (ψ : E2 → ℂ) : E2 → ℂ := fun x =>
  - d0 (d0 ψ) x - d1 (d1 ψ) x - 5 * d0 ψ x + (Real.tan (x 1) : ℂ) * d1 ψ x
    + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * ψ x

/-- The weight `α z^(p+1) cos θ` with `z = exp (α s)`, `p+1 = (5+2α)/α`. -/
def wt (α : ℝ) : E2 → ℝ := fun x =>
  α * (Real.exp (α * x 0)) ^ ((5 + 2 * α) / α) * Real.cos (x 1)

/-- The unknown of the strip problem: `V = α z · u` with `u = Ψ · ω`,
`ω = z^((5+α)/α) cos θ`; zero outside the strip. -/
def Vfun (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * Ψ (Real.exp (α * x 0)) (x 1))

/-- The source of the strip problem: `G = α z · F · ω`; zero outside the strip. -/
def Gfun (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * F (Real.exp (α * x 0)) (x 1))

/-- The chart `(z,θ) ↦ ((1/α) log z, θ)` from the quadrant to the strip. -/
def chart (α : ℝ) (p : ℝ × ℝ) : E2 := coords ((1 / α) * Real.log p.1) p.2

/-- The weak identity satisfied by the pair `(V, G)` on the strip: for every smooth compactly
supported test function supported in the strip, `∫ V · Kop ψ = ∫ G · ψ`.

This is the `(s,θ)`-form of the weak formulation of `bslOp α Ψ = F` for the unknown
`V = Vfun α Ψ` and the source `G = Gfun α F`. -/
def StripWeak (V G : E2 → ℂ) : Prop :=
  ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
    Function.support ψ ⊆ stripE → ∫ x, V x * Kop ψ x = ∫ x, G x * ψ x

end Work.EllipticEst.InteriorRegularity
