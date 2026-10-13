/-
# `Work.FTS.EllSol.EllPkgAux.mollTargetDeriv`

The log-radial derivative of the (uncurried) integrand `Hxyc G t s = Qext G (exp t) s` of the
double mollification, at the interior angle `θ ∈ (0, π/2)`:

`∂_t (∂_s Hxyc G t s)|_{s=θ}|_{t=log z} = D_z (∂_θ G) (z, θ)`.

Both sides are elementary: at an interior angle `θ` the doubly-odd extension `Qext` agrees with
the datum on a whole neighbourhood of `θ`, so the inner `s`-derivative is just `∂_θ G`; then
`t ↦ ∂_θG (exp t, θ)` is the composition of the `z`-slice `w ↦ ∂_θG (w, θ)` with `Real.exp`,
and the chain rule (with `exp (log z) = z`) produces the logarithmic derivative
`z · ∂_z∂_θG (z, θ) = D_z (∂_θG) (z, θ)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- The doubly-odd extension `Qext` agrees with the datum on a neighbourhood of every interior
angle, hence the two `θ`-derivatives at such an angle coincide. -/
theorem deriv_Qext_slice {G : ℝ → ℝ → ℝ} {w θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    deriv (fun y' => Work.FTS.EllSol.PkgK5.K5c.Qext G w y') θ
      = deriv (fun y' => G w y') θ := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from
    ⟨hθ0, hθ1⟩)] with y hy
  exact Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G w y ⟨hy.1.le, hy.2.le⟩

theorem mollTargetDeriv (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z) = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the inner `s`-derivative is the plain angular derivative of the datum
  have hinner : (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ)
      = fun x' => Work.Spaces.pth G (Real.exp x') θ := by
    funext x'
    exact deriv_Qext_slice (G := G) (w := Real.exp x') hθ0 hθ1
  rw [hinner]
  -- chain rule: `z`-slice of `∂_θG` composed with `Real.exp`, at `x = log z`
  have hF : HasDerivAt (fun w : ℝ => Work.Spaces.pth G w θ)
      (Work.Spaces.pz (Work.Spaces.pth G) z θ) z := hS.pth.hasDerivAt_slice hθ hz
  have hF' : HasDerivAt (fun w : ℝ => Work.Spaces.pth G w θ)
      (Work.Spaces.pz (Work.Spaces.pth G) z θ) (Real.exp (Real.log z)) := by
    rw [Real.exp_log hz]; exact hF
  have hcomp := HasDerivAt.comp (h := Real.exp) (x := Real.log z) hF'
    (Real.hasDerivAt_exp (Real.log z))
  have hderiv : deriv (fun x' => Work.Spaces.pth G (Real.exp x') θ) (Real.log z)
      = Work.Spaces.pz (Work.Spaces.pth G) z θ * Real.exp (Real.log z) := hcomp.deriv
  rw [hderiv, Real.exp_log hz]
  show Work.Spaces.pz (Work.Spaces.pth G) z θ * z = Work.Spaces.Dz (Work.Spaces.pth G) z θ
  rw [Work.Spaces.Dz]
  ring

end Work.FTS.EllSol.EllPkgAux
