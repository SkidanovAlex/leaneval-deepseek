import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-!
# Differentiability of `x ↦ F (ρ x) (θ x)`

The polar (spherical) coordinates `(ρ, θ)` are smooth functions of `x ∈ ℝ³` away from the
axis `r = 0`: `ρ = √(r² + x₃²)` is a composition of a smooth quadratic function with `√` (which
is differentiable off `0`), and `θ = arctan(x₃ / r)` is a composition of `arctan` with the
differentiable quotient `x₃ / r` (legitimate since `r ≠ 0` there).

Consequently, if `F` is differentiable as a function of two variables at the point
`(ρ x, θ x)`, then `y ↦ F (ρ y) (θ y)` is differentiable at `x`.  This is the composite
chain rule used to differentiate the reduced fields `F(ρ, θ)` of the paper.
-/

/-! ## Differentiability of the individual coordinates -/

/-- `ρ = √(radSq + axial²)` is differentiable away from the origin, i.e. whenever the radicand
does not vanish. -/
lemma differentiableAt_rho_of_ne (x : R3) (h : radSq x + axial x ^ 2 ≠ 0) :
    DifferentiableAt ℝ rho x := by
  have hcoord : ∀ i : Fin 3, DifferentiableAt ℝ (fun y : R3 => y i) x := fun i =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x i).differentiableAt
  have hradSq : DifferentiableAt ℝ (fun y : R3 => radSq y) x := by
    show DifferentiableAt ℝ (fun y : R3 => y 0 ^ 2 + y 1 ^ 2) x
    exact ((hcoord 0).pow 2).add ((hcoord 1).pow 2)
  have hax : DifferentiableAt ℝ (fun y : R3 => axial y) x := differentiableAt_axial x
  have hsum : DifferentiableAt ℝ (fun y : R3 => radSq y + axial y ^ 2) x :=
    hradSq.add (hax.pow 2)
  exact hsum.sqrt h

/-- `ρ` is differentiable at any point off the axis (`radial x > 0`). -/
lemma differentiableAt_rho_of_radial_pos (x : R3) (hr : 0 < radial x) :
    DifferentiableAt ℝ rho x := by
  refine differentiableAt_rho_of_ne x ?_
  have hpos : 0 < radSq x := by rw [← radial_sq]; exact pow_pos hr 2
  exact ne_of_gt (add_pos_of_pos_of_nonneg hpos (sq_nonneg _))

/-- `θ = arctan(axial / radial)` is differentiable at any point off the axis. -/
lemma differentiableAt_theta_of_radial_ne (x : R3) (hr : radial x ≠ 0) :
    DifferentiableAt ℝ theta x := by
  have hax : DifferentiableAt ℝ (fun y : R3 => axial y) x := differentiableAt_axial x
  have hradial : DifferentiableAt ℝ (fun y : R3 => radial y) x := differentiableAt_radial x hr
  have hdiv : DifferentiableAt ℝ (fun y : R3 => axial y / radial y) x :=
    hax.mul (hradial.inv hr)
  exact hdiv.arctan

/-! ## The composite chain rule -/

theorem differentiableAt_rho_theta_comp (F : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    DifferentiableAt ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hrho : DifferentiableAt ℝ rho x := differentiableAt_rho_of_radial_pos x hr
  have htheta : DifferentiableAt ℝ theta x := differentiableAt_theta_of_radial_ne x hrne
  have hpair : DifferentiableAt ℝ (fun y : R3 => (rho y, theta y)) x := hrho.prodMk htheta
  exact hF.comp x hpair

end Work.Cyl
