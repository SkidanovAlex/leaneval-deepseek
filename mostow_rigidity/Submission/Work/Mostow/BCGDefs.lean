import Mathlib
import Submission.Mostow.Interfaces

/-!
# Shared definitions for the BCG natural-map Jacobian computation (area N2)

All of the analysis for `NatMapJacProp` is phrased against the measure `sigma n` on `E n`,
using the explicit Poisson kernel

  `pfun n x ξ = (tpart x - ⟪x,ξ⟫) ^ (-(n-1)) = exp (-(n-1) * busemann ξ x)`

whose associated density measure `(sigma n).withDensity (ofReal ∘ pfun n x)` is `visual n x`.

The natural map is `F x = bar ((visual n x).map φ)`, i.e. the (unique) minimiser in `y` of

  `Phi n φ x y = ∫ ξ, pfun n x ξ * busemann (φ ξ) y ∂(sigma n)`,

and `Gv n φ x y` is its `y`-gradient (the "G" of the design), obtained by differentiating
under the integral: `∇_y busemann (φ ξ) · = gradB n (φ ξ) ·`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Poisson kernel: the density of `visual n x` with respect to `sigma n`. -/
def pfun (n : ℕ) (x ξ : E n) : ℝ := (tpart x - inner ℝ x ξ) ^ (-((n : ℝ) - 1))

/-- Derivative of `x ↦ pfun n x ξ` as a continuous linear functional. -/
def dpfun (n : ℕ) (x ξ : E n) : E n →L[ℝ] ℝ :=
  (-((n : ℝ) - 1) * (tpart x - inner ℝ x ξ) ^ (-((n : ℝ) - 1) - 1)) •
    ((tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ)

/-- Euclidean gradient of `y ↦ busemann ξ y`. -/
def gradB (n : ℕ) (ξ y : E n) : E n :=
  (tpart y - inner ℝ y ξ)⁻¹ • ((tpart y)⁻¹ • y - ξ)

/-- Euclidean Hessian of `y ↦ busemann ξ y`, as a continuous linear map. -/
def hessB (n : ℕ) (ξ y : E n) : E n →L[ℝ] E n :=
  let g := tpart y - inner ℝ y ξ
  let s := tpart y
  g⁻¹ • (s⁻¹ • (1 : E n →L[ℝ] E n) - (s ^ 3)⁻¹ • (innerSL ℝ y).smulRight y) -
    (innerSL ℝ (gradB n ξ y)).smulRight (gradB n ξ y)

/-- The barycentre functional of the pushed-forward visual measure, written against `sigma n`. -/
def Phi (n : ℕ) (φ : E n → E n) (x y : E n) : ℝ :=
  ∫ ξ, pfun n x ξ * busemann (φ ξ) y ∂(sigma n)

/-- The `y`-gradient of `Phi n φ x ·`, as a function of `(x,y)`. -/
def Gv (n : ℕ) (φ : E n → E n) (x y : E n) : E n :=
  ∫ ξ, pfun n x ξ • gradB n (φ ξ) y ∂(sigma n)

/-- Second-moment operator of the pushed-forward measure:
`w ↦ ∫ ⟪φ ξ, w⟫ • φ ξ ∂σ`, as an integral of continuous linear maps. -/
def Hlin (n : ℕ) (φ : E n → E n) : E n →L[ℝ] E n :=
  ∫ ξ, (innerSL ℝ (φ ξ)).smulRight (φ ξ) ∂(sigma n)

/-- The joint Fréchet derivative of `Gv`, obtained by differentiating under the integral. -/
def DGv (n : ℕ) (φ : E n → E n) (x y : E n) : (E n × E n) →L[ℝ] E n :=
  ∫ ξ, ((dpfun n x ξ).smulRight (gradB n (φ ξ) y)) ∘L ContinuousLinearMap.fst ℝ (E n) (E n) +
    (pfun n x ξ • hessB n (φ ξ) y) ∘L ContinuousLinearMap.snd ℝ (E n) (E n) ∂(sigma n)

/-- Tangent lift of a chart vector `v` at the chart point `y`: `(v, ⟪y,v⟫/tpart y)`. -/
def tanlift (n : ℕ) (y v : E n) : Fin n ⊕ Fin 1 → ℝ :=
  Sum.elim (fun i => v i) (fun _ => (inner ℝ y v) / tpart y)

/-- The hyperboloid geodesic through `y` with chart-velocity `v`, read off in the chart:
`t ↦ spat (cosh t • hlift y + sinh t • tanlift y v)`. For `gH y v = 1` this is the unit speed
geodesic, and for every chart vector `v` its derivative at `t = 0` is `v`. -/
def hgeo (n : ℕ) (y v : E n) (t : ℝ) : E n :=
  WithLp.toLp 2 (fun i => (Real.cosh t • hlift y + Real.sinh t • tanlift n y v) (Sum.inl i))

/-- The cross second-moment operator `v ↦ ∫ ⟪ξ,v⟫ • φ ξ ∂σ`. -/
def Slin (n : ℕ) (φ : E n → E n) : E n →L[ℝ] E n :=
  ∫ ξ, (innerSL ℝ ξ).smulRight (φ ξ) ∂(sigma n)

/-- `N = (n-1) • S`, the right hand side of `(I - H) ∘ DF(0) = N`. -/
def Nlin (n : ℕ) (φ : E n → E n) : E n →L[ℝ] E n :=
  ((n : ℝ) - 1) • Slin n φ

end

end Work.Mostow
