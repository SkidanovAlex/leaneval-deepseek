import Submission.Work.RPA3.Defs

/-!
# RPA3: the tubular (Weinstein-type) picture

The normal directions to the Lagrangian family `L.ℓ τ` are `J ∂_xℓ` and `J ∂_tℓ`, where
`J(q,p) = (p,-q)` is the `ω`-compatible complex structure of `Defs.lean`.  The *tubular
parametrisation*

`θ(τ,x,t,ξ) = ℓ τ (x,t) + J (ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)`

maps the strip `(τ,x,t,ξ)` onto a neighbourhood of the family; it is a local diffeomorphism
(the four vectors `∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ` are a basis, by `imm` and `lag`), and it is
injective on a small strip.  This is `D2` of the route design.
-/

open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- The tubular parametrisation of the neighbourhood of the Lagrangian family `L.ℓ τ`. -/
def theta (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) : PS :=
  L.ℓ τ (x, t) + J (ξ.1 • deriv (fun y => L.ℓ τ (y, t)) x + ξ.2 • deriv (fun s => L.ℓ τ (x, s)) t)

@[simp] theorem J_zero : J 0 = 0 := by
  ext <;> simp [J]

@[simp] theorem theta_zero (L : LagFamilyAll) (τ x t : ℝ) :
    theta L τ x t (0, 0) = L.ℓ τ (x, t) := by
  simp [theta]

/-- The tubular map in the strip coordinates `(x,t,ξ)`, at fixed `τ`; it is a local diffeomorphism
`PS → PS`. -/
def thetaZ (L : LagFamilyAll) (τ : ℝ) (z : PS) : PS :=
  theta L τ z.1.1 z.1.2 z.2

/-- The tubular map on `(τ,x,t,ξ)`, as a map `ℝ × PS → ℝ × PS`; this is the form in which the
inverse function theorem is applied (its derivative is invertible at every point of the strip). -/
def thetaP (L : LagFamilyAll) (w : ℝ × PS) : ℝ × PS :=
  (w.1, thetaZ L w.1 w.2)

@[simp] theorem thetaZ_apply (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    thetaZ L τ ((x, t), ξ) = theta L τ x t ξ := rfl

@[simp] theorem thetaP_apply (L : LagFamilyAll) (τ : ℝ) (z : PS) :
    thetaP L (τ, z) = (τ, thetaZ L τ z) := rfl

/-- The four vectors `∂_xθ, ∂_tθ, ∂_{ξ₁}θ, ∂_{ξ₂}θ` (columns of the derivative of the tubular map
`thetaZ L τ` at `(x,t,ξ)`) are linearly independent.  At `ξ = 0` this is the statement that
`(∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ)` is a basis, which follows from `LagFamilyAll.imm` and
`LagFamilyAll.lag`; for `ξ ≠ 0` it holds for small `‖ξ‖`. -/
def ColumnsIndependent (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) : Prop :=
  ∀ a b c d : ℝ,
    a • deriv (fun y => theta L τ y t ξ) x + b • deriv (fun s => theta L τ x s ξ) t
      + c • deriv (fun u => theta L τ x t (u, ξ.2)) ξ.1
      + d • deriv (fun u => theta L τ x t (ξ.1, u)) ξ.2 = 0 →
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

/-- `thetaP` has an invertible derivative at `w` (so it is a local diffeomorphism there). -/
def IsLocDiffeoAt (L : LagFamilyAll) (w : ℝ × PS) : Prop :=
  ∃ F' : (ℝ × PS) ≃L[ℝ] (ℝ × PS), HasFDerivAt (thetaP L) (F' : ℝ × PS →L[ℝ] (ℝ × PS)) w

end Work.RPA3
