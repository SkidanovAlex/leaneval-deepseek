import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

/-!
# Cylindrical / polar coordinates on ℝ³

This module sets up the coordinate functions, frames and field representations used by the
`Work.Cyl` layer, following §Setup of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on ℝ³*, Annals of Math. **194** (2021) 771--887.

Conventions.

* `ℝ³ = EuclideanSpace ℝ (Fin 3)` with coordinates indexed by `Fin 3`.  Coordinates `0` and `1`
  span the plane orthogonal to the symmetry axis, and coordinate `2` is the axis.  Thus the
  paper's `x₃` is the Lean coordinate `2` (`axial`), and the paper's `r` is the distance to the
  axis (`radial`).  This choice is forced by `FiniteTimeSingularity.IsOdd`, whose third
  conjunct is precisely oddness/evenness in coordinate `2`.
* `ρ = √(r² + x₃²)` is `rho` (and equals `‖x‖`), `θ = arctan (x₃/r)` is `theta`, and
  `R = ρ^α` is `Rc α`.
* All two-variable functions are curried, `f : ℝ → ℝ → ℝ`, `f r z`, with `r` the radial and `z`
  the axial variable.  `pdR`,`pdZ` are the partial derivatives `∂_r`, `∂_z` computed with
  `deriv` on the corresponding slice; `pdRR`, `pdZZ`, `pdRZ`, `pdZR` the second ones.
* Off the axis `x ↦ (r, x₃)` we have the cylindrical frame `e_r, e_θ, e₃`; `radialVec = r e_r`
  and `angularVec = r e_θ` are smooth across the axis and are the objects we use in
  definitions, so that the fields are defined everywhere.
* The no-swirl axisymmetric field with radial and axial components `u_r, u_z` (functions of
  `(r, x₃)`) is `cylField ur uz`; its "stream function" form is `psiField ψ`.
-/

noncomputable section

open scoped Matrix

namespace Work.Cyl

/-- `ℝ³`, the Euclidean space with the standard basis indexed by `Fin 3`.  Coordinates `0` and `1`
span the plane orthogonal to the symmetry axis; coordinate `2` is the axis (paper's `x₃`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The squared distance to the `x₃`-axis, `x₀² + x₁²`.  Smooth everywhere. -/
def radSq (x : R3) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- The distance `r > 0` to the `x₃`-axis. -/
def radial (x : R3) : ℝ := Real.sqrt (radSq x)

/-- The axial coordinate `x₃` (coordinate `2`). -/
def axial (x : R3) : ℝ := x 2

/-- `r e_r = (x₀, x₁, 0)`, extended smoothly to the axis. -/
def radialVec (x : R3) : R3 := !₂[x 0, x 1, 0]

/-- `r e_θ = (-x₁, x₀, 0)`, extended smoothly to the axis. -/
def angularVec (x : R3) : R3 := !₂[-x 1, x 0, 0]

/-- The unit radial vector `e_r = (x₀, x₁, 0)/r` (defined as `0` on the axis). -/
def eR (x : R3) : R3 := (1 / radial x) • radialVec x

/-- The unit angular vector `e_θ = (-x₁, x₀, 0)/r` (defined as `0` on the axis). -/
def eTheta (x : R3) : R3 := (1 / radial x) • angularVec x

/-- The standard basis vector `e₀`. -/
def e0 : R3 := FiniteTimeSingularity.e 0

/-- The standard basis vector `e₁`. -/
def e1 : R3 := FiniteTimeSingularity.e 1

/-- The unit axial vector `e₃`, the third standard basis vector. -/
def eZ : R3 := FiniteTimeSingularity.e 2

/-- The `i`-th standard basis vector of `ℝ³`. -/
def basisVec (i : Fin 3) : R3 := FiniteTimeSingularity.e i

@[simp] lemma basisVec_zero : basisVec 0 = e0 := rfl
@[simp] lemma basisVec_one : basisVec 1 = e1 := rfl
@[simp] lemma basisVec_two : basisVec 2 = eZ := rfl

/-- The partial derivative of a scalar field on `ℝ³` in the coordinate direction `i`, i.e. the
derivative of `t ↦ g (x + t • eᵢ)` at `t = 0`. -/
def pd (i : Fin 3) (g : R3 → ℝ) (x : R3) : ℝ :=
  deriv (fun t : ℝ => g (x + t • basisVec i)) 0

/-- `ρ = √(r² + x₃²)`, the three dimensional radius (equal to `‖x‖`). -/
def rho (x : R3) : ℝ := Real.sqrt (radSq x + axial x ^ 2)

/-- `θ = arctan(x₃/r)`, the polar angle from the plane `x₃ = 0`; defined on `r > 0`. -/
def theta (x : R3) : ℝ := Real.arctan (axial x / radial x)

/-- `R = ρ^α`. -/
def Rc (α : ℝ) (x : R3) : ℝ := rho x ^ α

/-- The radial component of a field, `u · e_r`. -/
def compR (u : R3 → R3) (x : R3) : ℝ := inner ℝ (u x) (eR x)

/-- The angular component of a field, `u · e_θ`. -/
def compT (u : R3 → R3) (x : R3) : ℝ := inner ℝ (u x) (eTheta x)

/-- The axial component of a field, `u · e₃`. -/
def compZ (u : R3 → R3) (x : R3) : ℝ := inner ℝ (u x) eZ

/-! ## Two-variable calculus on the `(r, x₃)` half plane -/

/-- `∂_r f`, the partial derivative in the radial variable of a function of `(r, x₃)`. -/
def pdR (f : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := deriv (fun r' => f r' z) r

/-- `∂_z f`, the partial derivative in the axial variable of a function of `(r, x₃)`. -/
def pdZ (f : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := deriv (fun z' => f r z') z

/-- `∂_rr f`. -/
def pdRR (f : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := deriv (fun r' => pdR f r' z) r

/-- `∂_zz f`. -/
def pdZZ (f : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := deriv (fun z' => pdZ f r z') z

/-- `∂_r ∂_z f`. -/
def pdRZ (f : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := deriv (fun r' => pdZ f r' z) r

/-- `∂_z ∂_r f`. -/
def pdZR (f : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := deriv (fun z' => pdR f r z') z

/-- `f` is differentiable as a function of two variables at `(r, z)`. -/
abbrev DiffAt2 (f : ℝ → ℝ → ℝ) (r z : ℝ) : Prop :=
  DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z)

/-! ## The polar change of variables `(r, x₃) ↦ (ρ, θ)` -/

/-- `ρ = √(r² + z²)` for a function of `(r, z)`. -/
def rhoP (r z : ℝ) : ℝ := Real.sqrt (r ^ 2 + z ^ 2)

/-- `θ = arctan(z/r)` for a function of `(r, z)`. -/
def thetaP (r z : ℝ) : ℝ := Real.arctan (z / r)

/-- `R = ρ^α` for a function of `(r, z)`. -/
def RP (α : ℝ) (r z : ℝ) : ℝ := rhoP r z ^ α

/-! ## Representations of axisymmetric no-swirl fields -/

/-- The axisymmetric no-swirl velocity field with *reduced* radial profile `a` and axial profile
`b`:  `x ↦ a(r², x₃) • (x₀, x₁, 0) + b(r², x₃) • e₃`.  This is defined and smooth across the
axis, and the radial component is `u_r = r · a(r², x₃)`. -/
def axiField (a b : ℝ → ℝ → ℝ) : R3 → R3 :=
  fun x => a (radSq x) (axial x) • radialVec x + b (radSq x) (axial x) • eZ

/-- The axisymmetric no-swirl velocity field with radial component `u_r` and axial component
`u_z`, both functions of `(r, x₃)`:  `x ↦ (u_r(r,x₃)/r) • (x₀,x₁,0) + u_z(r,x₃) • e₃`.  Off the
axis this equals `u_r e_r + u_z e_z`; on the axis it is `u_z(0,x₃) e₃`. -/
def cylField (ur uz : ℝ → ℝ → ℝ) : R3 → R3 :=
  fun x => (ur (radial x) (axial x) / radial x) • radialVec x + uz (radial x) (axial x) • eZ

/-- The reduced radial profile `u_r / r` of a no-swirl field, as a function of `(r, x₃)`. -/
def redR (ur : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun r z => ur r z / r

/-- The velocity field associated with the stream function `ψ`:
`u_r = ∂_z ψ`, `u_z = -(1/r) ψ - ∂_r ψ` (paper (PsiTou)). -/
def psiField (ψ : ℝ → ℝ → ℝ) : R3 → R3 :=
  cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z)

/-- The scalar vorticity `ω^θ(r,x₃) = ∂_z u_r - ∂_r u_z` of a no-swirl axisymmetric field, i.e.
the `e_θ`-component of `∇ × u`. -/
def vortTheta (ur uz : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ := pdZ ur r z - pdR uz r z

/-- The axisymmetric Biot--Savart / elliptic operator of (3dBSL):
`Lψ = -∂_rrψ - ∂_zzψ - (1/r)∂_rψ + ψ/r²`. -/
def cylOp (ψ : ℝ → ℝ → ℝ) (r z : ℝ) : ℝ :=
  -pdRR ψ r z - pdZZ ψ r z - pdR ψ r z / r + ψ r z / r ^ 2

/-- `IsAxiNoSwirl u`: `u` is an axisymmetric field without swirl, i.e. it is of the form
`u = u_r(r,x₃) e_r + u_z(r,x₃) e₃` with `u_r, u_z` functions of `(r, x₃)` only. -/
def IsAxiNoSwirl (u : R3 → R3) : Prop :=
  ∃ ur uz : ℝ → ℝ → ℝ, u = cylField ur uz

/-! ## Parity in the axial variable -/

/-- `f` is even in the axial variable. -/
def EvenZ (f : ℝ → ℝ → ℝ) : Prop := ∀ r z, f r (-z) = f r z

/-- `f` is odd in the axial variable. -/
def OddZ (f : ℝ → ℝ → ℝ) : Prop := ∀ r z, f r (-z) = -f r z

/-- `f` is even in the axial variable on the half plane `r ≥ 0`. -/
def EvenZnn (f : ℝ → ℝ → ℝ) : Prop := ∀ r, 0 ≤ r → ∀ z, f r (-z) = f r z

/-- `f` is odd in the axial variable on the half plane `r ≥ 0`.  This is the parity that the
no-swirl field `cylField` sees (it only evaluates the profiles at `radial x ≥ 0`). -/
def OddZnn (f : ℝ → ℝ → ℝ) : Prop := ∀ r, 0 ≤ r → ∀ z, f r (-z) = -f r z

/-- Reflection in the axis coordinate. -/
def reflZ (x : R3) : R3 := !₂[x 0, x 1, -x 2]

/-- Reflection in the first coordinate. -/
def refl0 (x : R3) : R3 := !₂[-x 0, x 1, x 2]

/-- Reflection in the second coordinate. -/
def refl1 (x : R3) : R3 := !₂[x 0, -x 1, x 2]

/-- `u` is even in the axial coordinate: `u(reflZ x) = u x`. -/
def EvenInZ (u : R3 → R3) : Prop := ∀ x, u (reflZ x) = u x

/-- Flip the first component of a vector. -/
def flip0 (v : R3) : R3 := !₂[-v 0, v 1, v 2]

/-- Flip the second component of a vector. -/
def flip1 (v : R3) : R3 := !₂[v 0, -v 1, v 2]

/-- Flip the third (axial) component of a vector. -/
def flipZ (v : R3) : R3 := !₂[v 0, v 1, -v 2]

end Work.Cyl
